Require Import CoqOfNoir.CoqOfNoir.

(*
  fn test_base64_decode_with_padding$f0() -> () {
      let input$0 = [71, 120, 77, 108, 103, 119, 76, 105, 121, 2⁴×7, 110, 86, 114, 69, 50, 67, 2⁴×3, 83, 102, 52, 121, 122, 104, 99, 87, 84, 107, 65, 104, 83, 90, 53, 43, 87, 69, 82, 104, 75, 104, 88, 116, 108, 85, 61];
      let result$1 = base64_decode$f1(input$l0);
      let expected$2 = [27, 19, 37, 131, 2, 226, 202, 153, 213, 172, 77, 130, 209, 39, 248, 203, 56, 92, 89, 57, 0, 133, 38, 121, 249, 97, 17, 132, 168, 87, 182, 85];
      constrain eq$f2(result$l1, expected$l2)
  }
*)
Definition test_base64_decode_with_padding₀ (α : list Value.t) : M.t :=
  match α with
  | [] =>
    let* result :=
      let~ input := [[ M.copy (|
        M.alloc (Value.Array [
          M.read (| M.alloc (Value.Integer IntegerKind.U8 71) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 120) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 77) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 108) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 103) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 119) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 76) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 105) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 121) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 112) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 110) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 86) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 114) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 69) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 50) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 67) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 48) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 83) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 102) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 121) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 122) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 104) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 99) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 87) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 84) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 107) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 65) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 104) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 83) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 90) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 53) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 43) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 87) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 69) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 82) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 104) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 75) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 104) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 88) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 116) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 108) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 85) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 61) |)
        ])
      |) ]] in
      let~ result := [[ M.copy (|
        M.alloc (M.call_closure (|
          M.read (| M.get_function (| "base64_decode", 1 |) |),
          [
            M.read (| input |)
          ]
        |))
      |) ]] in
      let~ expected := [[ M.copy (|
        M.alloc (Value.Array [
          M.read (| M.alloc (Value.Integer IntegerKind.U8 27) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 19) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 37) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 131) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 2) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 226) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 202) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 153) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 213) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 172) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 77) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 130) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 209) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 39) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 248) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 203) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 56) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 92) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 89) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 57) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 133) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 38) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 121) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 249) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 97) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 17) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 132) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 168) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 87) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 182) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 85) |)
        ])
      |) ]] in
      [[
        M.alloc (M.assert (|
          M.read (| M.alloc (M.call_closure (|
            M.read (| M.get_function (| "eq", 2 |) |),
            [
              M.read (| result |);
              M.read (| expected |)
            ]
          |)) |),
          None
        |))
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

(*
  fn base64_decode$f1(input$l3: [u8; 44]) -> [u8; 32] {
      let decoded$4 = base64_decode_elements$f3(input$l3);
      let result$5 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
      let BASE64_ELEMENTS_PER_CHUNK$6 = 40;
      let BYTES_PER_CHUNK$7 = 30;
      let num_chunks$8 = ((44 / BASE64_ELEMENTS_PER_CHUNK$l6) + (((44 % BASE64_ELEMENTS_PER_CHUNK$l6) != 0) as u32));
      if (num_chunks$l8 > 0) {
          for i$9 in 0 .. (num_chunks$l8 - 1) {
              let slice$10 = 0;
              for j$11 in 0 .. BASE64_ELEMENTS_PER_CHUNK$l6 {
                  slice$l10 = (slice$l10 * 2⁶);
                  slice$l10 = (slice$l10 + (decoded$l4[((i$l9 * BASE64_ELEMENTS_PER_CHUNK$l6) + j$l11)] as Field))
              };
              let slice_bytes$12 = to_be_bytes$f4(slice$l10);
              for j$13 in 0 .. BYTES_PER_CHUNK$l7 {
                  result$l5[((i$l9 * BYTES_PER_CHUNK$l7) + j$l13)] = slice_bytes$l12[j$l13]
              }
          };
          let base64_elements_in_final_chunk$14 = (44 - ((num_chunks$l8 - 1) * BASE64_ELEMENTS_PER_CHUNK$l6));
          let slice$15 = 0;
          for j$16 in 0 .. base64_elements_in_final_chunk$l14 {
              slice$l15 = (slice$l15 * 2⁶);
              slice$l15 = (slice$l15 + (decoded$l4[(((num_chunks$l8 - 1) * BASE64_ELEMENTS_PER_CHUNK$l6) + j$l16)] as Field))
          };
          for _$17 in base64_elements_in_final_chunk$l14 .. BASE64_ELEMENTS_PER_CHUNK$l6 {
              slice$l15 = (slice$l15 * 2⁶)
          };
          let slice_bytes$18 = to_be_bytes$f4(slice$l15);
          let num_bytes_in_final_chunk$19 = (2⁵ - ((num_chunks$l8 - 1) * BYTES_PER_CHUNK$l7));
          for i$20 in 0 .. num_bytes_in_final_chunk$l19 {
              result$l5[(((num_chunks$l8 - 1) * BYTES_PER_CHUNK$l7) + i$l20)] = slice_bytes$l18[i$l20]
          }
      };
      result$l5
  }
*)
Definition base64_decode₁ (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let input := M.alloc input in
    let* result :=
      let~ decoded := [[ M.copy (|
        M.alloc (M.call_closure (|
          M.read (| M.get_function (| "base64_decode_elements", 3 |) |),
          [
            M.read (| input |)
          ]
        |))
      |) ]] in
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |)
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
            M.read (| M.alloc (Value.Integer IntegerKind.U32 44) |),
            M.read (| BASE64_ELEMENTS_PER_CHUNK |)
          |)) |),
          M.read (| M.alloc (M.cast (|
            M.read (| M.alloc (Binary.not_equal (|
              M.read (| M.alloc (Binary.modulo (|
                M.read (| M.alloc (Value.Integer IntegerKind.U32 44) |),
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
                  M.read (| M.get_function (| "to_be_bytes", 4 |) |),
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
              M.read (| M.alloc (Value.Integer IntegerKind.U32 44) |),
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
              M.read (| M.get_function (| "to_be_bytes", 4 |) |),
              [
                M.read (| slice |)
              ]
            |))
          |) ]] in
          let~ num_bytes_in_final_chunk := [[ M.copy (|
            M.alloc (Binary.subtract (|
              M.read (| M.alloc (Value.Integer IntegerKind.U32 32) |),
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
  fn eq$f2(self$l21: [u8; 32], other$l22: [u8; 32]) -> bool {
      let result$23 = true;
      for i$24 in 0 .. len$array_len(self$l21) {
          result$l23 = (result$l23 & eq$f5(self$l21[i$l24], other$l22[i$l24]))
      };
      result$l23
  }
*)
Definition eq₂ (α : list Value.t) : M.t :=
  match α with
  | [self; other] =>
    let self := M.alloc self in
    let other := M.alloc other in
    let* result :=
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Bool true)
      |) ]] in
      do~ [[
        M.for_ (|
          M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
          M.read (| M.alloc (M.call_closure (|
            M.read (| Builtin.len |),
            [
              M.read (| self |)
            ]
          |)) |),
          fun (i : Value.t) =>
          [[
            M.alloc (M.assign (|
              M.read (| M.alloc (result) |),
              M.read (| M.alloc (Binary.and_ (|
                M.read (| result |),
                M.read (| M.alloc (M.call_closure (|
                  M.read (| M.get_function (| "eq", 5 |) |),
                  [
                    M.read (| M.alloc (M.index (|
                      M.read (| self |),
                      M.read (| i |)
                    |)) |);
                    M.read (| M.alloc (M.index (|
                      M.read (| other |),
                      M.read (| i |)
                    |)) |)
                  ]
                |)) |)
              |)) |)
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
  fn base64_decode_elements$f3(input$l25: [u8; 44]) -> [u8; 44] {
      let Base64Decoder$26 = new$f6();
      let result$27 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
      for i$28 in 0 .. 44 {
          let input_byte$29 = input$l25[i$l28];
          result$l27[i$l28] = get$f7(Base64Decoder$l26, (input_byte$l29 as Field));
          constrain (result$l27[i$l28] != 255)
      };
      result$l27
  }
*)
Definition base64_decode_elements₃ (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let input := M.alloc input in
    let* result :=
      let~ Base64Decoder := [[ M.copy_mutable (|
        M.alloc (M.call_closure (|
          M.read (| M.get_function (| "new", 6 |) |),
          []
        |))
      |) ]] in
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |)
        ])
      |) ]] in
      do~ [[
        M.for_ (|
          M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
          M.read (| M.alloc (Value.Integer IntegerKind.U32 44) |),
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
                M.read (| M.get_function (| "get", 7 |) |),
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
  fn to_be_bytes$f4(self$l30: Field) -> [u8; 30] {
      let bytes$31 = to_be_radix$f8(self$l30, 2⁸);
      if (!is_unconstrained$is_unconstrained()) {
          let p$32 = &[2⁴×3, 100, 78, 114, 225, 49, 2⁴×10, 41, 184, 2⁴×5, 69, 182, 129, 129, 88, 93, 40, 51, 232, 72, 121, 185, 2⁴×7, 145, 67, 225, 245, 147, 2⁴×15, 0, 0, 1];
          constrain (len$array_len(bytes$l31) <= len$array_len(p$l32));
          let ok$33 = (len$array_len(bytes$l31) != len$array_len(p$l32));
          for i$34 in 0 .. 30 {
              if (!ok$l33) {
                  if (bytes$l31[i$l34] != p$l32[i$l34]) {
                      constrain (bytes$l31[i$l34] < p$l32[i$l34]);
                      ok$l33 = true
                  }
              }
          };
          constrain ok$l33
      };
      bytes$l31
  }
*)
Definition to_be_bytes₄ (α : list Value.t) : M.t :=
  match α with
  | [self] =>
    let self := M.alloc self in
    let* result :=
      let~ bytes := [[ M.copy (|
        M.alloc (M.call_closure (|
          M.read (| M.get_function (| "to_be_radix", 8 |) |),
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
  fn eq$f5(self$l35: u8, other$l36: u8) -> bool {
      (self$l35 == other$l36)
  }
*)
Definition eq₅ (α : list Value.t) : M.t :=
  match α with
  | [self; other] =>
    let self := M.alloc self in
    let other := M.alloc other in
    let* result :=
      [[
        M.alloc (Binary.equal (|
          M.read (| self |),
          M.read (| other |)
        |))
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

(*
  fn new$f6() -> ([u8; 256]) {
      {
          let table$37 = [255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 62, 255, 255, 255, 63, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 255, 255, 255, 255, 255, 255, 255, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 2⁴, 17, 18, 19, 20, 21, 22, 23, 24, 25, 255, 255, 255, 255, 255, 255, 26, 27, 28, 29, 30, 31, 2⁵, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 2⁴×3, 49, 50, 51, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255, 255];
          (table$l37)
      }
  }
*)
Definition new₆ (α : list Value.t) : M.t :=
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
  fn get$f7(self$l38: ([u8; 256]), idx$l39: Field) -> u8 {
      self$l38.0[idx$l39]
  }
*)
Definition get₇ (α : list Value.t) : M.t :=
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
  fn to_be_radix$f8(self$l40: Field, radix$l41: u32) -> [u8; 30] {
      assert_constant$assert_constant(radix$l41);;
      __to_be_radix$to_be_radix(self$l40, radix$l41)
  }
*)
Definition to_be_radix₈ (α : list Value.t) : M.t :=
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
