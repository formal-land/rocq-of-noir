import json
import sys


def indent(text: str) -> str:
    return "\n".join("  " + line for line in text.split("\n"))


def paren(with_paren: bool, text: str) -> str:
    return f"({text})" if with_paren else text


def integer_to_subscript(integer: int) -> str:
    return "".join("₀₁₂₃₄₅₆₇₈₉"[int(digit)] for digit in str(integer))


def name_id_to_rocq(name: str, index: int) -> str:
    return f"{name}{integer_to_subscript(index)}"


def parameters_to_rocq(parameters: list) -> list[str]:
    return [parameter[2] for parameter in parameters]


'''
pub enum Definition {
    Local(LocalId),
    Global(GlobalId),
    Function(FuncId),
    Builtin(String),
    LowLevel(String),
    // used as a foreign/externally defined unconstrained function
    Oracle(String),
}

pub struct Ident {
    pub location: Option<Location>,
    pub definition: Definition,
    pub mutable: bool,
    pub name: String,
    pub typ: Type,
}
'''
def ident_to_rocq(function_table: dict[str, list[int]], node) -> str:
    definition_node = node["definition"]
    definition_node_type: str = list(definition_node.keys())[0]

    if definition_node_type == "Local":
        definition_node = definition_node["Local"]
        return node["name"]

    if definition_node_type == "Global":
        definition_node = definition_node["Global"]
        return alloc("get_global \"" + node["name"] + "\" " + str(definition_node))

    if definition_node_type == "Function":
        definition_node = definition_node["Function"]
        index = function_table[node["name"]].index(definition_node)
        return alloc("get_function \"" + node["name"] + "\" " + str(index))

    if definition_node_type == "Builtin":
        definition_node = definition_node["Builtin"]
        return "Builtin." + node["name"]

    if definition_node_type == "LowLevel":
        definition_node = definition_node["LowLevel"]
        return alloc("get_low_level \"" + node["name"] + "\"")

    if definition_node_type == "Oracle":
        definition_node = definition_node["Oracle"]
        return "Oracle." + node["name"]

    raise Exception(f"Unknown node type: {definition_node_type}")


'''
pub struct ArrayLiteral {
    pub contents: Vec<Expression>,
    pub typ: Type,
}
'''
def array_literal_to_rocq(function_table: dict[str, list[int]], node) -> str:
    return \
        "[\n" + \
        indent(
            ";\n".join(
                read(expression_to_rocq(function_table, expression))
                for expression in node["contents"]
            )
         ) + "\n" + \
        "]"


def escape_string(string: str) -> str:
    return string.replace("\"", "\"\"")


'''
pub enum Signedness {
    Unsigned,
    Signed,
}

pub enum IntegerBitSize {
    One,
    Eight,
    Sixteen,
    ThirtyTwo,
    SixtyFour,
}

pub enum Type {
    Field,
    Integer(Signedness, /*bits:*/ IntegerBitSize), // u32 = Integer(unsigned, ThirtyTwo)
    // ...
}
'''
def type_to_integer_kind(node) -> str:
    if node == "Field":
        raise Exception("Unexpected Field type")

    node_type = list(node.keys())[0]

    if node_type == "Integer":
        node = node["Integer"]
        bit_sizes: dict[str, int] = {
            "One": 1,
            "Eight": 8,
            "Sixteen": 16,
            "ThirtyTwo": 32,
            "SixtyFour": 64,
        }
        if node[0] == "Unsigned":
            return f"IntegerKind.U{bit_sizes[node[1]]}"
        if node[0] == "Signed":
            return f"IntegerKind.S{bit_sizes[node[1]]}"

    raise Exception(f"Unknown node type: {node_type}")


'''
pub enum Literal {
    Array(ArrayLiteral),
    Slice(ArrayLiteral),
    // false for positive integer and true for negative
    Integer(FieldElement, /*sign*/ bool, Type, Location),
    Bool(bool),
    Unit,
    Str(String),
    FmtStr(String, u64, Box<Expression>),
}
'''
def literal_to_rocq(function_table: dict[str, list[int]], node) -> str:
    node_type: str = list(node.keys())[0]

    if node_type == "Array":
        node = node["Array"]
        return "Value.Array " + array_literal_to_rocq(function_table, node)

    if node_type == "Slice":
        node = node["Slice"]
        return "Value.Slice " + array_literal_to_rocq(function_table, node)

    if node_type == "Integer":
        node = node["Integer"]
        if node[2] == "Field":
            return "Value.Field " + str(int(node[0], 16))
        return \
            "Value.Integer " + \
            type_to_integer_kind(node[2]) + " " + \
            ("(-" if node[1] else "") + \
            str(int(node[0], 16)) + \
            (")" if node[1] else "")

    if node_type == "Bool":
        node = node["Bool"]
        return "Value.Bool " + "true" if node else "false"

    if node_type == "Unit":
        return "Value.Tuple []"

    if node_type == "Str":
        node = node["Str"]
        return "Value.String \"" + escape_string(node) + "\""

    if node_type == "FmtStr":
        node = node["FmtStr"]
        return \
            "Value.fmt_str " + \
            "\"" + escape_string(node[0]) + "\" " + \
            str(node[1]) + \
            paren(True, expression_to_rocq(function_table, node[2]))

    raise Exception(f"Unknown node type: {node_type}")


def camel_case_to_snake_case(string: str) -> str:
    return "".join(
        "_" + char.lower() if char.isupper() else char
        for char in string
    ).lstrip("_")


'''
pub struct Unary {
    pub operator: crate::ast::UnaryOp,
    pub rhs: Box<Expression>,
    pub result_type: Type,
    pub location: Location,
}
'''
def unary_to_rocq(function_table: dict[str, list[int]], node) -> str:
    return alloc(
        "Unary." + camel_case_to_snake_case(node["operator"]) + " (|\n" +
        indent(read(expression_to_rocq(function_table, node["rhs"]))) + "\n" +
        "|)"
    )


'''
pub struct Binary {
    pub lhs: Box<Expression>,
    pub operator: BinaryOp,
    pub rhs: Box<Expression>,
    pub location: Location,
}
'''
def binary_to_rocq(function_table: dict[str, list[int]], node) -> str:
    operator = camel_case_to_snake_case(node["operator"])
    reserved_operators = ["and", "or"]
    if operator in reserved_operators:
        operator += "_"
    return alloc(
        "Binary." + operator + " (|\n" +
        indent(
            read(expression_to_rocq(function_table, node["lhs"])) + ",\n" +
            read(expression_to_rocq(function_table, node["rhs"]))
        ) + "\n" + \
        "|)"
    )


'''
pub struct Index {
    pub collection: Box<Expression>,
    pub index: Box<Expression>,
    pub element_type: Type,
    pub location: Location,
}
'''
def index_to_rocq(function_table: dict[str, list[int]], node) -> str:
    return \
        "M.index (|\n" + \
        indent(
            expression_to_rocq(function_table, node["collection"]) + ",\n" +
            read(expression_to_rocq(function_table, node["index"]))
        ) + "\n" + \
        "|)"


'''
pub struct Cast {
    pub lhs: Box<Expression>,
    pub r#type: Type,
    pub location: Location,
}
'''
def cast_to_rocq(function_table: dict[str, list[int]], node) -> str:
    if node["type"] == "Field":
        return alloc(
            "M.cast_to_field (|\n" +
            indent(
                read(expression_to_rocq(function_table, node["lhs"]))
            ) + "\n" +
            "|)"
        )
    return alloc(
        "M.cast (|\n" +
        indent(
            read(expression_to_rocq(function_table, node["lhs"])) + ",\n" +
            type_to_integer_kind(node["type"])
        ) + "\n" +
        "|)"
    )


'''
pub struct For {
    pub index_variable: LocalId,
    pub index_name: String,
    pub index_type: Type,

    pub start_range: Box<Expression>,
    pub end_range: Box<Expression>,
    pub block: Box<Expression>,

    pub start_range_location: Location,
    pub end_range_location: Location,
}
'''
def for_to_rocq(function_table: dict[str, list[int]], node) -> str:
    return \
        "M.for_ (|\n" + \
        indent(
            read(expression_to_rocq(function_table, node["start_range"])) + ",\n" +
            read(expression_to_rocq(function_table, node["end_range"])) + ",\n" +
            "fun (" + node["index_name"] + " : Value.t) =>\n" +
            expression_to_rocq(function_table, node["block"])
        ) + "\n" + \
        "|)"


'''
pub struct If {
    pub condition: Box<Expression>,
    pub consequence: Box<Expression>,
    pub alternative: Option<Box<Expression>>,
    pub typ: Type,
}
'''
def if_to_rocq(function_table: dict[str, list[int]], node) -> str:
    return \
        "M.if_ (|\n" + \
        indent(
            read(expression_to_rocq(function_table, node["condition"])) + ",\n" +
            expression_to_rocq(function_table, node["consequence"]) + ",\n" +
            (
                "(Some (" + expression_to_rocq(function_table, node["alternative"]) + "))"
                if node["alternative"] is not None
                else "None"
            )
        ) + "\n" + \
        "|)"


'''
pub struct Call {
    pub func: Box<Expression>,
    pub arguments: Vec<Expression>,
    pub return_type: Type,
    pub location: Location,
}
'''
def call_to_rocq(function_table: dict[str, list[int]], node) -> str:
    return alloc(
        "M.call_closure (|\n" +
        indent(
            read(expression_to_rocq(function_table, node["func"])) + ",\n" +
            (
                (
                    "[\n" +
                    indent(
                        ";\n".join(
                            read(expression_to_rocq(function_table, expression))
                            for expression in node["arguments"]
                        )
                    ) + "\n" +
                    "]"
                ) if len(node["arguments"]) != 0
                else "[]"
             )
        ) + "\n" +
        "|)"
    )


'''
pub struct Let {
    pub id: LocalId,
    pub mutable: bool,
    pub name: String,
    pub expression: Box<Expression>,
}
'''
def let_to_rocq(function_table: dict[str, list[int]], node) -> str:
    copy_function = "copy_mutable" if node["mutable"] else "copy"

    return \
        "let~ " + \
        node["name"] + " := [[ M." + copy_function + " (|\n" + \
        indent(expression_to_rocq(function_table, node["expression"])) + "\n" + \
        "|) ]] in"


'''
pub enum LValue {
    Ident(Ident),
    Index { array: Box<LValue>, index: Box<Expression>, element_type: Type, location: Location },
    MemberAccess { object: Box<LValue>, field_index: usize },
    Dereference { reference: Box<LValue>, element_type: Type },
}
'''
def lvalue_to_rocq(function_table: dict[str, list[int]], node) -> str:
    node_type: str = list(node.keys())[0]

    if node_type == "Ident":
        node = node["Ident"]
        return alloc(ident_to_rocq(function_table, node))

    if node_type == "Index":
        node = node["Index"]
        return alloc(
            "M.index (|\n" +
            indent(
                read(lvalue_to_rocq(function_table, node["array"])) + ",\n" +
                read(expression_to_rocq(function_table, node["index"]))
            ) + "\n" +
            "|)"
        )

    if node_type == "MemberAccess":
        node = node["MemberAccess"]
        return alloc(
            "M.member_access (|\n" +
            indent(
                read(lvalue_to_rocq(function_table, node["object"])) + ",\n" +
                str(node["field_index"])
            ) + "\n" +
            "|)"
        )

    if node_type == "Dereference":
        node = node["Dereference"]
        return read(lvalue_to_rocq(function_table, node["reference"]))

    raise Exception(f"Unknown node type: {node_type}")


'''
pub struct Assign {
    pub lvalue: LValue,
    pub expression: Box<Expression>,
}
'''
def assign_to_rocq(function_table: dict[str, list[int]], node) -> str:
    return alloc(
        "M.write (|\n" +
        indent(
            read(lvalue_to_rocq(function_table, node["lvalue"])) + ",\n" +
            read(expression_to_rocq(function_table, node["expression"]))
        ) + "\n" + \
        "|)"
    )


def expression_inside_block_to_rocq(function_table: dict[str, list[int]], node, is_last: bool) -> str:
    node_type: str = list(node.keys())[0]

    if node_type == "Let":
        node = node["Let"]
        return let_to_rocq(function_table, node)

    if is_last:
        return \
            "[[\n" + \
            indent(expression_to_rocq(function_table, node)) + "\n" + \
            "]]"

    return \
        "do~ [[\n" + \
        indent(expression_to_rocq(function_table, node)) + "\n" + \
        "]] in"


def alloc(expression: str) -> str:
    return "M.alloc (" + expression + ")"


def read(expression: str) -> str:
    # If the expression is an alloc
    alloc_beginning = "M.alloc ("
    alloc_end = ")"
    if expression.startswith(alloc_beginning) and expression.endswith(alloc_end):
        return expression[len(alloc_beginning):-len(alloc_end)]
    return "M.read (| " + expression + " |)"


def write(expression: str, value: str) -> str:
    return \
        "M.write (|\n" + \
        indent(
            expression + ",\n" +
            value
        ) + "\n" + \
        "|)"


'''
pub enum Expression {
    Ident(Ident),
    Literal(Literal),
    Block(Vec<Expression>),
    Unary(Unary),
    Binary(Binary),
    Index(Index),
    Cast(Cast),
    For(For),
    If(If),
    Tuple(Vec<Expression>),
    ExtractTupleField(Box<Expression>, usize),
    Call(Call),
    Let(Let),
    Constrain(Box<Expression>, Location, Option<Box<(Expression, HirType)>>),
    Assign(Assign),
    Semi(Box<Expression>),
    Break,
    Continue,
}
'''
def expression_to_rocq(function_table: dict[str, list[int]], node) -> str:
    node_type: str = list(node.keys())[0]

    if node_type == "Ident":
        node = node["Ident"]
        return ident_to_rocq(function_table, node)

    if node_type == "Literal":
        node = node["Literal"]
        return alloc(literal_to_rocq(function_table, node))

    if node_type == "Block":
        node = node["Block"]
        return \
            "\n".join(
                expression_inside_block_to_rocq(function_table, expression, index == len(node) - 1)
                for index, expression in enumerate(node)
            )

    if node_type == "Unary":
        node = node["Unary"]
        return unary_to_rocq(function_table, node)

    if node_type == "Binary":
        node = node["Binary"]
        return binary_to_rocq(function_table, node)

    if node_type == "Index":
        node = node["Index"]
        return index_to_rocq(function_table, node)

    if node_type == "Cast":
        node = node["Cast"]
        return cast_to_rocq(function_table, node)

    if node_type == "For":
        node = node["For"]
        return for_to_rocq(function_table, node)

    if node_type == "If":
        node = node["If"]
        return if_to_rocq(function_table, node)

    if node_type == "Tuple":
        node = node["Tuple"]
        return alloc(
            "Value.Tuple [" +
            "; ".join(read(expression_to_rocq(function_table, expression)) for expression in node) +
            "]"
        )

    if node_type == "ExtractTupleField":
        node = node["ExtractTupleField"]
        return \
            "M.extract_tuple_field (|\n" + \
            indent(
                indent(expression_to_rocq(function_table, node[0])) + ",\n" + \
                str(node[1])
            ) + "\n" + \
            "|)"

    if node_type == "Call":
        node = node["Call"]
        return call_to_rocq(function_table, node)

    if node_type == "Let":
        node = node["Let"]
        return let_to_rocq(function_table, node)

    if node_type == "Constrain":
        node = node["Constrain"]
        return alloc(
            "M.assert (|\n" + \
            indent(
                read(expression_to_rocq(function_table, node[0])) + ",\n" + \
                (
                    "Some (" + read(expression_to_rocq(function_table, node[2][0])) + ")"
                    if node[2] is not None
                    else "None"
                )
            ) + "\n" + \
            "|)"
        )

    if node_type == "Assign":
        node = node["Assign"]
        return assign_to_rocq(function_table, node)

    if node_type == "Semi":
        node = node["Semi"]
        # We have no additional printing for this case!
        return expression_to_rocq(function_table, node)

    if node_type == "Break":
        return "Break"

    if node_type == "Continue":
        return "Continue"

    raise Exception(f"Unknown node type: {node_type}")


'''
pub struct Function {
    pub id: FuncId,
    pub name: String,

    pub parameters: Parameters,
    pub body: Expression,

    pub return_type: Type,
    pub unconstrained: bool,
    pub inline_type: InlineType,
    pub func_sig: FunctionSignature,
}
'''
def function_to_rocq(function_table: dict[str, list[int]], node) -> str:
    index = function_table[node['name']].index(node['id'])
    parameters = parameters_to_rocq(node["parameters"])
    return \
        "(*\n" + \
        indent(node['source_code'].replace("(*", "( *").strip()) + "\n" + \
        "*)\n" + \
        f"Definition {name_id_to_rocq(node['name'], index)} (α : list Value.t) " + \
        ": M.t :=\n" + \
        indent(
            "match α with\n" +
            "| [" + "; ".join(parameters) + "] =>\n" +
            indent(
                "".join(
                    "let " + parameter + " := M.alloc " + parameter + " in\n"
                    for parameter in parameters
                ) +
                "let* result :=\n" +
                indent(expression_to_rocq(function_table, node["body"])) + " in\n" +
                "M.read result"
            ) + "\n" +
            "| _ => M.impossible \"wrong number of arguments\"\n" +
            "end."
        ) + "\n" + \
        "\n" + \
        "Axiom get_function_" + name_id_to_rocq(node['name'], index) + " :\n" + \
        indent (
            "get_function \"" + node['name'] + "\" " + str(index) + " =\n" + \
            "closure " + name_id_to_rocq(node['name'], index) + "."
        ) + "\n" + \
        "Global Hint Rewrite get_function_" + \
        name_id_to_rocq(node['name'], index) + " : get_function."


def program_to_rocq(node) -> str:
    function_table: dict[str, list[int]] = {}

    for function in reversed(node["functions"]):
        function_table[function["name"]] = \
            function_table.get(function["name"], []) + [function["id"]]

    return "\n\n".join(
        function_to_rocq(function_table, function)
        for function in reversed(node["functions"]
    ))


def main():
    # Open the JSON of the file path given as command line argument
    input_path = sys.argv[1]
    with open(input_path, "r") as f:
        noir = json.load(f)

    # Print the Coq code
    print("Require Import RocqOfNoir.RocqOfNoir.")
    print()
    print(program_to_rocq(noir))


if __name__ == "__main__":
    main()
