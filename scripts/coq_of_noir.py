import json
import sys


def indent(text: str) -> str:
    return "\n".join("  " + line for line in text.split("\n"))


def name_id_to_coq(name: str, id: int) -> str:
    return f"{name}ᵢ{id}"


def parameters_to_coq(parameters: list) -> list[str]:
    return [parameter[2] for parameter in parameters]


'''
pub enum Definition {
    Local(LocalId),
    Function(FuncId),
    Builtin(String),
    LowLevel(String),
    // used as a foreign/externally defined unconstrained function
    Oracle(String),
}
'''
def definition_to_coq(node) -> str:
    node_type: str = list(node.keys())[0]

    if node_type == "Local":
        node = node["Local"]
        return f"Local {node}"

    if node_type == "Function":
        node = node["Function"]
        return f"Function {node}"

    if node_type == "Builtin":
        node = node["Builtin"]
        return f"Builtin {node}"

    if node_type == "LowLevel":
        node = node["LowLevel"]
        return f"LowLevel {node}"

    if node_type == "Oracle":
        node = node["Oracle"]
        return f"Oracle {node}"

    raise Exception(f"Unknown node type: {node_type}")


'''
pub struct Ident {
    pub location: Option<Location>,
    pub definition: Definition,
    pub mutable: bool,
    pub name: String,
    pub typ: Type,
}
'''
def ident_to_coq(node) -> str:
    return node["name"] + "/" + definition_to_coq(node["definition"])


'''
pub struct ArrayLiteral {
    pub contents: Vec<Expression>,
    pub typ: Type,
}
'''
def array_literal_to_coq(node) -> str:
    return \
        "[" + \
        ", ".join(expression_to_coq(expression) for expression in node["contents"]) + \
        "]"


'''
pub enum Literal {
    Array(ArrayLiteral),
    Slice(ArrayLiteral),
    Integer(FieldElement, /*sign*/ bool, Type, Location), // false for positive integer and true for negative
    Bool(bool),
    Unit,
    Str(String),
    FmtStr(String, u64, Box<Expression>),
}
'''
def literal_to_coq(node) -> str:
    node_type: str = list(node.keys())[0]

    if node_type == "Array":
        node = node["Array"]
        return array_literal_to_coq(node)

    if node_type == "Slice":
        node = node["Slice"]
        return array_literal_to_coq(node)

    if node_type == "Integer":
        node = node["Integer"]
        return \
            ("-" if node[1] else "") + \
            node[0]

    if node_type == "Bool":
        node = node["Bool"]
        return "true" if node else "false"

    if node_type == "Unit":
        return "tt"

    if node_type == "Str":
        node = node["Str"]
        return "\"" + node + "\""

    if node_type == "FmtStr":
        node = node["FmtStr"]
        return \
            "FmtStr (" + \
            node[0] + ", " + \
            str(node[1]) + ", " + \
            expression_to_coq(node[2]) + ")"

    raise Exception(f"Unknown node type: {node_type}")


'''
pub struct Unary {
    pub operator: crate::ast::UnaryOp,
    pub rhs: Box<Expression>,
    pub result_type: Type,
    pub location: Location,
}
'''
def unary_to_coq(node) -> str:
    return \
        "Unary " + \
        node["operator"] + " " + \
        expression_to_coq(node["rhs"])


'''
pub struct Binary {
    pub lhs: Box<Expression>,
    pub operator: BinaryOp,
    pub rhs: Box<Expression>,
    pub location: Location,
}
'''
def binary_to_coq(node) -> str:
    return \
        "Binary " + \
        expression_to_coq(node["lhs"]) + " " + \
        node["operator"] + " " + \
        expression_to_coq(node["rhs"])


'''
pub struct Index {
    pub collection: Box<Expression>,
    pub index: Box<Expression>,
    pub element_type: Type,
    pub location: Location,
}
'''
def index_to_coq(node) -> str:
    return \
        "Index " + \
        expression_to_coq(node["collection"]) + " " + \
        expression_to_coq(node["index"])


'''
pub struct Cast {
    pub lhs: Box<Expression>,
    pub r#type: Type,
    pub location: Location,
}
'''
def cast_to_coq(node) -> str:
    return \
        "Cast " + \
        expression_to_coq(node["lhs"]) + " " + \
        json.dumps(node["type"])


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
def for_to_coq(node) -> str:
    return \
        "For " + \
        node["index_name"] + " " + \
        expression_to_coq(node["start_range"]) + " " + \
        expression_to_coq(node["end_range"]) + "\n" + \
        indent(expression_to_coq(node["block"]))


'''
pub struct If {
    pub condition: Box<Expression>,
    pub consequence: Box<Expression>,
    pub alternative: Option<Box<Expression>>,
    pub typ: Type,
}
'''
def if_to_coq(node) -> str:
    return \
        "If " + \
        expression_to_coq(node["condition"]) + " " + \
        expression_to_coq(node["consequence"]) + " " + \
        (
            "(Some " + expression_to_coq(node["alternative"]) + ")"
            if node["alternative"] is not None
            else "None"
        )


'''
pub struct Call {
    pub func: Box<Expression>,
    pub arguments: Vec<Expression>,
    pub return_type: Type,
    pub location: Location,
}
'''
def call_to_coq(node) -> str:
    return \
        "Call " + \
        expression_to_coq(node["func"]) + " " + \
        "[" + \
        ", ".join(expression_to_coq(expression) for expression in node["arguments"]) + \
        "]"


'''
pub struct Let {
    pub id: LocalId,
    pub mutable: bool,
    pub name: String,
    pub expression: Box<Expression>,
}
'''
def let_to_coq(node) -> str:
    return \
        "Let " + \
        node["name"] + " :=\n" + \
        indent(expression_to_coq(node["expression"]))


'''
pub enum LValue {
    Ident(Ident),
    Index { array: Box<LValue>, index: Box<Expression>, element_type: Type, location: Location },
    MemberAccess { object: Box<LValue>, field_index: usize },
    Dereference { reference: Box<LValue>, element_type: Type },
}
'''
def lvalue_to_coq(node) -> str:
    node_type: str = list(node.keys())[0]

    if node_type == "Ident":
        node = node["Ident"]
        return ident_to_coq(node)

    if node_type == "Index":
        node = node["Index"]
        return \
            "Index " + \
            lvalue_to_coq(node["array"]) + " " + \
            expression_to_coq(node["index"])

    if node_type == "MemberAccess":
        node = node["MemberAccess"]
        return \
            "MemberAccess " + \
            lvalue_to_coq(node["object"]) + " " + \
            node["field_index"]

    if node_type == "Dereference":
        node = node["Dereference"]
        return \
            "Dereference " + \
            lvalue_to_coq(node["reference"])

    raise Exception(f"Unknown node type: {node_type}")


'''
pub struct Assign {
    pub lvalue: LValue,
    pub expression: Box<Expression>,
}
'''
def assign_to_coq(node) -> str:
    return \
        "Assign " + \
        lvalue_to_coq(node["lvalue"]) + " " + \
        expression_to_coq(node["expression"])


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
def expression_to_coq(node) -> str:
    node_type: str = list(node.keys())[0]

    if node_type == "Ident":
        node = node["Ident"]
        return ident_to_coq(node)

    if node_type == "Literal":
        node = node["Literal"]
        return literal_to_coq(node)

    if node_type == "Block":
        node = node["Block"]
        return \
            "do\n" + \
            indent(
                "\n".join(expression_to_coq(expression) for expression in node)
            )

    if node_type == "Unary":
        node = node["Unary"]
        return unary_to_coq(node)

    if node_type == "Binary":
        node = node["Binary"]
        return binary_to_coq(node)

    if node_type == "Index":
        node = node["Index"]
        return index_to_coq(node)

    if node_type == "Cast":
        node = node["Cast"]
        return cast_to_coq(node)

    if node_type == "For":
        node = node["For"]
        return for_to_coq(node)

    if node_type == "If":
        node = node["If"]
        return if_to_coq(node)

    if node_type == "Tuple":
        node = node["Tuple"]
        return \
            "Tuple [" + \
            ", ".join(expression_to_coq(expression) for expression in node) + \
            "]"

    if node_type == "ExtractTupleField":
        node = node["ExtractTupleField"]
        return \
            "ExtractTupleField " + \
            expression_to_coq(node[0]) + " " + \
            str(node[1])

    if node_type == "Call":
        node = node["Call"]
        return call_to_coq(node)

    if node_type == "Let":
        node = node["Let"]
        return let_to_coq(node)

    if node_type == "Constrain":
        node = node["Constrain"]
        return \
            "Constrain " + \
            expression_to_coq(node[0]) + " " + \
            (
                "(Some " + expression_to_coq(node[2][0]) + ")"
                if node[2] is not None
                else "None"
            )

    if node_type == "Assign":
        node = node["Assign"]
        return assign_to_coq(node)

    if node_type == "Semi":
        node = node["Semi"]
        return \
            "Semi " + \
            expression_to_coq(node)

    if node_type == "Break":
        return "Break"

    if node_type == "Continue":
        return "Continue"

    raise Exception(f"Unknown node type: {node_type}")

def function_to_coq(node) -> str:
    parameters = parameters_to_coq(node["parameters"])
    return \
        f"Definition {name_id_to_coq(node['name'], node['id'])} (α : list Value.t) " + \
        ": M.t Value.t :=\n" + \
        indent(
            "match α with\n" +
            "| [" + ", ".join(parameters) + "] =>\n" +
            indent(expression_to_coq(node["body"])) + "\n" +
            "| _ => M.impossible \"wrong number of arguments\"\n" +
            "end."
        )



def program_to_coq(node) -> str:
    return "\n\n".join(function_to_coq(function) for function in node["functions"])


def main():
    # Open the JSON of the file path given as command line argument
    input_path = sys.argv[1]
    with open(input_path, "r") as f:
        noir = json.load(f)

    # Print the Coq code
    print("Require Import CoqOfNoir.")
    print()
    print(program_to_coq(noir))


if __name__ == "__main__":
    main()
