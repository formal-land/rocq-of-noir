Require Import CoqOfNoir.CoqOfNoir.

(*
  fn test_decode_invalid$f0() -> () {
      let input$0 = [255];
      let _$1 = base64_decode$f1(input$l0)
  }
*)
Definition test_decode_invalid₀ (α : list Value.t) : M.t :=
  match α with
  | [] =>
    let* result :=
      let~ input := [[ M.copy (|
        M.alloc (Value.Array [
          M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |)
        ])
      |) ]] in
      let~ _ := [[ M.copy (|
        M.alloc (M.call_closure (|
          M.read (| M.get_function (| "base64_decode", 1 |) |),
          [
            M.read (| input |)
          ]
        |))
      |) ]] in in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

(*
  fn base64_decode$f1(input$l2: [u8; 1]) -> [u8; 0] {
      let decoded$3 = base64_decode_elements$f2(input$l2);
      let result$4 = [];
      let BASE64_ELEMENTS_PER_CHUNK$5 = 40;
      let BYTES_PER_CHUNK$6 = 30;
      let num_chunks$7 = ((1 / BASE64_ELEMENTS_PER_CHUNK$l5) + (((1 % BASE64_ELEMENTS_PER_CHUNK$l5) != 0) as u32));
      if (num_chunks$l7 > 0) {
          for i$8 in 0 .. (num_chunks$l7 - 1) {
              let slice$9 = 0;
              for j$10 in 0 .. BASE64_ELEMENTS_PER_CHUNK$l5 {
                  slice$l9 = (slice$l9 * 2⁶);
                  slice$l9 = (slice$l9 + (decoded$l3[((i$l8 * BASE64_ELEMENTS_PER_CHUNK$l5) + j$l10)] as Field))
              };
              let slice_bytes$11 = to_be_bytes$f3(slice$l9);
              for j$12 in 0 .. BYTES_PER_CHUNK$l6 {
                  result$l4[((i$l8 * BYTES_PER_CHUNK$l6) + j$l12)] = slice_bytes$l11[j$l12]
              }
          };
          let base64_elements_in_final_chunk$13 = (1 - ((num_chunks$l7 - 1) * BASE64_ELEMENTS_PER_CHUNK$l5));
          let slice$14 = 0;
          for j$15 in 0 .. base64_elements_in_final_chunk$l13 {
              slice$l14 = (slice$l14 * 2⁶);
              slice$l14 = (slice$l14 + (decoded$l3[(((num_chunks$l7 - 1) * BASE64_ELEMENTS_PER_CHUNK$l5) + j$l15)] as Field))
          };
          for _$16 in base64_elements_in_final_chunk$l13 .. BASE64_ELEMENTS_PER_CHUNK$l5 {
              slice$l14 = (slice$l14 * 2⁶)
          };
          let slice_bytes$17 = to_be_bytes$f3(slice$l14);
          let num_bytes_in_final_chunk$18 = (0 - ((num_chunks$l7 - 1) * BYTES_PER_CHUNK$l6));
          for i$19 in 0 .. num_bytes_in_final_chunk$l18 {
              result$l4[(((num_chunks$l7 - 1) * BYTES_PER_CHUNK$l6) + i$l19)] = slice_bytes$l17[i$l19]
          }
      };
      result$l4
  }
*)
Definition base64_decode₁ (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let input := M.alloc input in
    let* result :=
      let~ decoded := [[ M.copy (|
        M.alloc (M.call_closure (|
          M.read (| M.get_function (| "base64_decode_elements", 2 |) |),
          [
            M.read (| input |)
          ]
        |))
      |) ]] in
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          
        ])
      |) ]] in
      let~ BASE64_ELEMENTS_PER_CHUNK := [[ M.copy (|
        M.alloc (Value.Integer IntegerKind.U32 40)
      |) ]] in
      let~ BYTES_PER_CHUNK := [[ M.copy (|
        M.alloc (Value.Integer IntegerKind.U32 30)
      |) ]] in
      let~ num_chunks := [[ M.copy (|
        M.alloc (Binary.add (|
          M.read (| M.alloc (Binary.divide (|
            M.read (| M.alloc (Value.Integer IntegerKind.U32 1) |),
            M.read (| BASE64_ELEMENTS_PER_CHUNK |)
          |)) |),
          M.read (| M.alloc (M.cast (|
            M.read (| M.alloc (Binary.not_equal (|
              M.read (| M.alloc (Binary.modulo (|
                M.read (| M.alloc (Value.Integer IntegerKind.U32 1) |),
                M.read (| BASE64_ELEMENTS_PER_CHUNK |)
              |)) |),
              M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |)
            |)) |),
            IntegerKind.U32
          |)) |)
        |))
      |) ]] in
      do~ [[
        M.if_ (|
          M.read (| M.alloc (Binary.greater (|
            M.read (| num_chunks |),
            M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |)
          |)) |),
          do~ [[
            M.for_ (|
              M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
              M.read (| M.alloc (Binary.subtract (|
                M.read (| num_chunks |),
                M.read (| M.alloc (Value.Integer IntegerKind.U32 1) |)
              |)) |),
              fun (i : Value.t) =>
              let~ slice := [[ M.copy_mutable (|
                M.alloc (Value.Integer IntegerKind.Field 0)
              |) ]] in
              do~ [[
                M.for_ (|
                  M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
                  M.read (| BASE64_ELEMENTS_PER_CHUNK |),
                  fun (j : Value.t) =>
                  do~ [[
                    M.alloc (M.assign (|
                      M.read (| M.alloc (slice) |),
                      M.read (| M.alloc (Binary.multiply (|
                        M.read (| slice |),
                        M.read (| M.alloc (Value.Integer IntegerKind.Field 64) |)
                      |)) |)
                    |))
                  ]] in
                  [[
                    M.alloc (M.assign (|
                      M.read (| M.alloc (slice) |),
                      M.read (| M.alloc (Binary.add (|
                        M.read (| slice |),
                        M.read (| M.alloc (M.cast (|
                          M.read (| M.alloc (M.index (|
                            M.read (| decoded |),
                            M.read (| M.alloc (Binary.add (|
                              M.read (| M.alloc (Binary.multiply (|
                                M.read (| i |),
                                M.read (| BASE64_ELEMENTS_PER_CHUNK |)
                              |)) |),
                              M.read (| j |)
                            |)) |)
                          |)) |),
                          IntegerKind.Field
                        |)) |)
                      |)) |)
                    |))
                  ]]
                |)
              ]] in
              let~ slice_bytes := [[ M.copy (|
                M.alloc (M.call_closure (|
                  M.read (| M.get_function (| "to_be_bytes", 3 |) |),
                  [
                    M.read (| slice |)
                  ]
                |))
              |) ]] in
              [[
                M.for_ (|
                  M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
                  M.read (| BYTES_PER_CHUNK |),
                  fun (j : Value.t) =>
                  [[
                    M.alloc (M.assign (|
                      M.read (| M.alloc (M.index (|
                        M.read (| M.alloc (result) |),
                        M.read (| M.alloc (Binary.add (|
                          M.read (| M.alloc (Binary.multiply (|
                            M.read (| i |),
                            M.read (| BYTES_PER_CHUNK |)
                          |)) |),
                          M.read (| j |)
                        |)) |)
                      |)) |),
                      M.read (| M.alloc (M.index (|
                        M.read (| slice_bytes |),
                        M.read (| j |)
                      |)) |)
                    |))
                  ]]
                |)
              ]]
            |)
          ]] in
          let~ base64_elements_in_final_chunk := [[ M.copy (|
            M.alloc (Binary.subtract (|
              M.read (| M.alloc (Value.Integer IntegerKind.U32 1) |),
              M.read (| M.alloc (Binary.multiply (|
                M.read (| M.alloc (Binary.subtract (|
                  M.read (| num_chunks |),
                  M.read (| M.alloc (Value.Integer IntegerKind.U32 1) |)
                |)) |),
                M.read (| BASE64_ELEMENTS_PER_CHUNK |)
              |)) |)
            |))
          |) ]] in
          let~ slice := [[ M.copy_mutable (|
            M.alloc (Value.Integer IntegerKind.Field 0)
          |) ]] in
          do~ [[
            M.for_ (|
              M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
              M.read (| base64_elements_in_final_chunk |),
              fun (j : Value.t) =>
              do~ [[
                M.alloc (M.assign (|
                  M.read (| M.alloc (slice) |),
                  M.read (| M.alloc (Binary.multiply (|
                    M.read (| slice |),
                    M.read (| M.alloc (Value.Integer IntegerKind.Field 64) |)
                  |)) |)
                |))
              ]] in
              [[
                M.alloc (M.assign (|
                  M.read (| M.alloc (slice) |),
                  M.read (| M.alloc (Binary.add (|
                    M.read (| slice |),
                    M.read (| M.alloc (M.cast (|
                      M.read (| M.alloc (M.index (|
                        M.read (| decoded |),
                        M.read (| M.alloc (Binary.add (|
                          M.read (| M.alloc (Binary.multiply (|
                            M.read (| M.alloc (Binary.subtract (|
                              M.read (| num_chunks |),
                              M.read (| M.alloc (Value.Integer IntegerKind.U32 1) |)
                            |)) |),
                            M.read (| BASE64_ELEMENTS_PER_CHUNK |)
                          |)) |),
                          M.read (| j |)
                        |)) |)
                      |)) |),
                      IntegerKind.Field
                    |)) |)
                  |)) |)
                |))
              ]]
            |)
          ]] in
          do~ [[
            M.for_ (|
              M.read (| base64_elements_in_final_chunk |),
              M.read (| BASE64_ELEMENTS_PER_CHUNK |),
              fun (_ : Value.t) =>
              [[
                M.alloc (M.assign (|
                  M.read (| M.alloc (slice) |),
                  M.read (| M.alloc (Binary.multiply (|
                    M.read (| slice |),
                    M.read (| M.alloc (Value.Integer IntegerKind.Field 64) |)
                  |)) |)
                |))
              ]]
            |)
          ]] in
          let~ slice_bytes := [[ M.copy (|
            M.alloc (M.call_closure (|
              M.read (| M.get_function (| "to_be_bytes", 3 |) |),
              [
                M.read (| slice |)
              ]
            |))
          |) ]] in
          let~ num_bytes_in_final_chunk := [[ M.copy (|
            M.alloc (Binary.subtract (|
              M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
              M.read (| M.alloc (Binary.multiply (|
                M.read (| M.alloc (Binary.subtract (|
                  M.read (| num_chunks |),
                  M.read (| M.alloc (Value.Integer IntegerKind.U32 1) |)
                |)) |),
                M.read (| BYTES_PER_CHUNK |)
              |)) |)
            |))
          |) ]] in
          [[
            M.for_ (|
              M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
              M.read (| num_bytes_in_final_chunk |),
              fun (i : Value.t) =>
              [[
                M.alloc (M.assign (|
                  M.read (| M.alloc (M.index (|
                    M.read (| M.alloc (result) |),
                    M.read (| M.alloc (Binary.add (|
                      M.read (| M.alloc (Binary.multiply (|
                        M.read (| M.alloc (Binary.subtract (|
                          M.read (| num_chunks |),
                          M.read (| M.alloc (Value.Integer IntegerKind.U32 1) |)
                        |)) |),
                        M.read (| BYTES_PER_CHUNK |)
                      |)) |),
                      M.read (| i |)
                    |)) |)
                  |)) |),
                  M.read (| M.alloc (M.index (|
                    M.read (| slice_bytes |),
                    M.read (| i |)
                  |)) |)
                |))
              ]]
            |)
          ]],
          None
        |)
      ]] in
      [[
        result
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

(*
  fn base64_decode_elements$f2(input$l20: [u8; 1]) -> [u8; 1] {
      let Base64Decoder$21 = new$f4();
      let result$22 = [0];
      for i$23 in 0 .. 1 {
          let input_byte$24 = input$l20[i$l23];
          result$l22[i$l23] = get$f5(Base64Decoder$l21, (input_byte$l24 as Field));
          constrain (result$l22[i$l23] != 255)
      };
      result$l22
  }
*)
Definition base64_decode_elements₂ (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let input := M.alloc input in
    let* result :=
      let~ Base64Decoder := [[ M.copy_mutable (|
        M.alloc (M.call_closure (|
          M.read (| M.get_function (| "new", 4 |) |),
          []
        |))
      |) ]] in
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |)
        ])
      |) ]] in
      do~ [[
        M.for_ (|
          M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
          M.read (| M.alloc (Value.Integer IntegerKind.U32 1) |),
          fun (i : Value.t) =>
          let~ input_byte := [[ M.copy (|
            M.alloc (M.index (|
              M.read (| input |),
              M.read (| i |)
            |))
          |) ]] in
          do~ [[
            M.alloc (M.assign (|
              M.read (| M.alloc (M.index (|
                M.read (| M.alloc (result) |),
                M.read (| i |)
              |)) |),
              M.read (| M.alloc (M.call_closure (|
                M.read (| M.get_function (| "get", 5 |) |),
                [
                  M.read (| Base64Decoder |);
                  M.read (| M.alloc (M.cast (|
                    M.read (| input_byte |),
                    IntegerKind.Field
                  |)) |)
                ]
              |)) |)
            |))
          ]] in
          [[
            M.alloc (M.assert (|
              M.read (| M.alloc (Binary.not_equal (|
                M.read (| M.alloc (M.index (|
                  M.read (| result |),
                  M.read (| i |)
                |)) |),
                M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |)
              |)) |),
              Some (M.read (| M.alloc (Value.fmt_str "DecodeError: invalid symbol {input_byte}, offset {i}." 2(M.alloc (Value.Tuple [M.read (| input_byte |); M.read (| i |)]))) |))
            |))
          ]]
        |)
      ]] in
      [[
        result
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

(*
  fn to_be_bytes$f3(self$l25: Field) -> [u8; 30] {
      let bytes$26 = to_be_radix$f6(self$l25, 2⁸);
      if (!is_unconstrained$is_unconstrained()) {
          let p$27 = &[2⁴×3, 100, 78, 114, 225, 49, 2⁴×10, 41, 184, 2⁴×5, 69, 182, 129, 129, 88, 93, 40, 51, 232, 72, 121, 185, 2⁴×7, 145, 67, 225, 245, 147, 2⁴×15, 0, 0, 1];
          constrain (len$array_len(bytes$l26) <= len$array_len(p$l27));
          let ok$28 = (len$array_len(bytes$l26) != len$array_len(p$l27));
          for i$29 in 0 .. 30 {
              if (!ok$l28) {
                  if (bytes$l26[i$l29] != p$l27[i$l29]) {
                      constrain (bytes$l26[i$l29] < p$l27[i$l29]);
                      ok$l28 = true
                  }
              }
          };
          constrain ok$l28
      };
      bytes$l26
  }
*)
Definition to_be_bytes₃ (α : list Value.t) : M.t :=
  match α with
  | [self] =>
    let self := M.alloc self in
    let* result :=
      let~ bytes := [[ M.copy (|
        M.alloc (M.call_closure (|
          M.read (| M.get_function (| "to_be_radix", 6 |) |),
          [
            M.read (| self |);
            M.read (| M.alloc (Value.Integer IntegerKind.U32 256) |)
          ]
        |))
      |) ]] in
      do~ [[
        M.if_ (|
          M.read (| M.alloc (Unary.not (|
            M.read (| M.alloc (M.call_closure (|
              M.read (| Builtin.is_unconstrained |),
              []
            |)) |)
          |)) |),
          let~ p := [[ M.copy (|
            M.alloc (Value.Slice [
              M.read (| M.alloc (Value.Integer IntegerKind.U8 48) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 100) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 78) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 114) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 225) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 49) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 160) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 41) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 184) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 80) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 69) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 182) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 129) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 129) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 88) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 93) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 40) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 51) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 232) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 72) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 121) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 185) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 112) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 145) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 67) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 225) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 245) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 147) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 240) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
              M.read (| M.alloc (Value.Integer IntegerKind.U8 1) |)
            ])
          |) ]] in
          do~ [[
            M.alloc (M.assert (|
              M.read (| M.alloc (Binary.less_equal (|
                M.read (| M.alloc (M.call_closure (|
                  M.read (| Builtin.len |),
                  [
                    M.read (| bytes |)
                  ]
                |)) |),
                M.read (| M.alloc (M.call_closure (|
                  M.read (| Builtin.len |),
                  [
                    M.read (| p |)
                  ]
                |)) |)
              |)) |),
              None
            |))
          ]] in
          let~ ok := [[ M.copy_mutable (|
            M.alloc (Binary.not_equal (|
              M.read (| M.alloc (M.call_closure (|
                M.read (| Builtin.len |),
                [
                  M.read (| bytes |)
                ]
              |)) |),
              M.read (| M.alloc (M.call_closure (|
                M.read (| Builtin.len |),
                [
                  M.read (| p |)
                ]
              |)) |)
            |))
          |) ]] in
          do~ [[
            M.for_ (|
              M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
              M.read (| M.alloc (Value.Integer IntegerKind.U32 30) |),
              fun (i : Value.t) =>
              [[
                M.if_ (|
                  M.read (| M.alloc (Unary.not (|
                    M.read (| ok |)
                  |)) |),
                  [[
                    M.if_ (|
                      M.read (| M.alloc (Binary.not_equal (|
                        M.read (| M.alloc (M.index (|
                          M.read (| bytes |),
                          M.read (| i |)
                        |)) |),
                        M.read (| M.alloc (M.index (|
                          M.read (| p |),
                          M.read (| i |)
                        |)) |)
                      |)) |),
                      do~ [[
                        M.alloc (M.assert (|
                          M.read (| M.alloc (Binary.less (|
                            M.read (| M.alloc (M.index (|
                              M.read (| bytes |),
                              M.read (| i |)
                            |)) |),
                            M.read (| M.alloc (M.index (|
                              M.read (| p |),
                              M.read (| i |)
                            |)) |)
                          |)) |),
                          None
                        |))
                      ]] in
                      [[
                        M.alloc (M.assign (|
                          M.read (| M.alloc (ok) |),
                          M.read (| M.alloc (Value.Bool true) |)
                        |))
                      ]],
                      None
                    |)
                  ]],
                  None
                |)
              ]]
            |)
          ]] in
          [[
            M.alloc (M.assert (|
              M.read (| ok |),
              None
            |))
          ]],
          None
        |)
      ]] in
      [[
        bytes
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

(*
  fn new$f4() -> ([u8; 256]) {
      {
          let table$30 = [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 62, 255, 255, 255, 63, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 255, 255, 255, 255, 255, 255, 255, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 2⁴, 17, 18, 19, 20, 21, 22, 23, 24, 25, 255, 255, 255, 255, 255, 255, 26, 27, 28, 29, 30, 31, 2⁵, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 2⁴×3, 49, 50, 51, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255];
          (table$l30)
      }
  }
*)
Definition new₄ (α : list Value.t) : M.t :=
  match α with
  | [] =>
    let* result :=
      [[
        let~ table := [[ M.copy (|
          M.alloc (Value.Array [
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 62) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 63) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 53) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 54) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 55) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 56) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 57) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 58) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 59) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 60) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 61) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 1) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 2) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 3) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 4) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 5) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 6) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 7) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 8) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 9) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 10) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 11) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 12) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 13) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 14) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 15) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 16) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 17) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 18) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 19) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 20) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 21) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 22) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 23) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 24) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 25) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 26) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 27) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 28) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 29) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 30) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 31) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 32) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 33) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 34) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 35) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 36) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 37) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 38) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 39) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 40) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 41) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 42) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 43) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 44) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 45) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 46) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 47) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 48) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 49) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 50) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 51) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 255) |)
          ])
        |) ]] in
        [[
          M.alloc (Value.Tuple [M.read (| table |)])
        ]]
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

(*
  fn get$f5(self$l31: ([u8; 256]), idx$l32: Field) -> u8 {
      self$l31.0[idx$l32]
  }
*)
Definition get₅ (α : list Value.t) : M.t :=
  match α with
  | [self; idx] =>
    let self := M.alloc self in
    let idx := M.alloc idx in
    let* result :=
      [[
        M.alloc (M.index (|
          M.read (| M.alloc (M.extract_tuple_field (|
              self,
            0
          |)) |),
          M.read (| idx |)
        |))
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

(*
  fn to_be_radix$f6(self$l33: Field, radix$l34: u32) -> [u8; 30] {
      assert_constant$assert_constant(radix$l34);;
      __to_be_radix$to_be_radix(self$l33, radix$l34)
  }
*)
Definition to_be_radix₆ (α : list Value.t) : M.t :=
  match α with
  | [self; radix] =>
    let self := M.alloc self in
    let radix := M.alloc radix in
    let* result :=
      do~ [[
        M.alloc (M.call_closure (|
          M.read (| Builtin.assert_constant |),
          [
            M.read (| radix |)
          ]
        |))
      ]] in
      [[
        M.alloc (M.call_closure (|
          M.read (| Builtin.__to_be_radix |),
          [
            M.read (| self |);
            M.read (| radix |)
          ]
        |))
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.
