Require Import CoqOfNoir.CoqOfNoir.

(*
  fn test_encode_utf8$f0() -> () {
      let input$0 = [227, 129, 147, 227, 130, 147, 227, 129, 171, 227, 129, 161, 227, 129, 175, 227, 2⁷, 129, 228, 184, 150, 231, 149, 140, 239, 188, 129];
      let expected$1 = [52, 52, 71, 84, 52, 52, 75, 84, 52, 52, 71, 114, 52, 52, 71, 104, 52, 52, 71, 118, 52, 52, 67, 66, 53, 76, 105, 87, 53, 53, 87, 77, 55, 55, 121, 66];
      let result$2 = base64_encode$f1(input$l0);
      constrain eq$f2(result$l2, expected$l1)
  }
*)
Definition test_encode_utf8₀ (α : list Value.t) : M.t :=
  match α with
  | [] =>
    let* result :=
      let~ input := [[ M.copy (|
        M.alloc (Value.Array [
          M.read (| M.alloc (Value.Integer IntegerKind.U8 227) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 129) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 147) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 227) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 130) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 147) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 227) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 129) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 171) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 227) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 129) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 161) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 227) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 129) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 175) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 227) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 128) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 129) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 228) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 184) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 150) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 231) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 149) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 140) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 239) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 188) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 129) |)
        ])
      |) ]] in
      let~ expected := [[ M.copy (|
        M.alloc (Value.Array [
          M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 71) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 84) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 75) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 84) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 71) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 114) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 71) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 104) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 71) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 118) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 67) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 66) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 53) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 76) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 105) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 87) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 53) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 53) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 87) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 77) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 55) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 55) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 121) |);
          M.read (| M.alloc (Value.Integer IntegerKind.U8 66) |)
        ])
      |) ]] in
      let~ result := [[ M.copy (|
        M.alloc (M.call_closure (|
          M.read (| M.get_function (| "base64_encode", 1 |) |),
          [
            M.read (| input |)
          ]
        |))
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
  fn base64_encode$f1(input$l3: [u8; 27]) -> [u8; 36] {
      let result$4 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
      let BASE64_ELEMENTS_PER_CHUNK$5 = 40;
      let BYTES_PER_CHUNK$6 = 30;
      let num_chunks$7 = ((27 / BYTES_PER_CHUNK$l6) + (((27 % BYTES_PER_CHUNK$l6) != 0) as u32));
      if (num_chunks$l7 > 0) {
          for i$8 in 0 .. (num_chunks$l7 - 1) {
              let slice$9 = 0;
              for j$10 in 0 .. BYTES_PER_CHUNK$l6 {
                  slice$l9 = (slice$l9 * 2⁸);
                  slice$l9 = (slice$l9 + (input$l3[((i$l8 * BYTES_PER_CHUNK$l6) + j$l10)] as Field))
              };
              let slice_base64_chunks$11 = to_be_radix$f3(slice$l9, 2⁶);
              for j$12 in 0 .. BASE64_ELEMENTS_PER_CHUNK$l5 {
                  result$l4[((i$l8 * BASE64_ELEMENTS_PER_CHUNK$l5) + j$l12)] = slice_base64_chunks$l11[j$l12]
              }
          };
          let bytes_in_final_chunk$13 = (27 - ((num_chunks$l7 - 1) * BYTES_PER_CHUNK$l6));
          let slice$14 = 0;
          for j$15 in 0 .. bytes_in_final_chunk$l13 {
              slice$l14 = (slice$l14 * 2⁸);
              slice$l14 = (slice$l14 + (input$l3[(((num_chunks$l7 - 1) * BYTES_PER_CHUNK$l6) + j$l15)] as Field))
          };
          for _$16 in bytes_in_final_chunk$l13 .. BYTES_PER_CHUNK$l6 {
              slice$l14 = (slice$l14 * 2⁸)
          };
          let slice_base64_chunks$17 = to_be_radix$f3(slice$l14, 2⁶);
          let num_elements_in_final_chunk$18 = (36 - ((num_chunks$l7 - 1) * BASE64_ELEMENTS_PER_CHUNK$l5));
          for i$19 in 0 .. num_elements_in_final_chunk$l18 {
              result$l4[(((num_chunks$l7 - 1) * BASE64_ELEMENTS_PER_CHUNK$l5) + i$l19)] = slice_base64_chunks$l17[i$l19]
          };
          result$l4 = base64_encode_elements$f4(result$l4)
      };
      result$l4
  }
*)
Definition base64_encode₁ (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let input := M.alloc input in
    let* result :=
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
            M.read (| M.alloc (Value.Integer IntegerKind.U32 27) |),
            M.read (| BYTES_PER_CHUNK |)
          |)) |),
          M.read (| M.alloc (M.cast (|
            M.read (| M.alloc (Binary.not_equal (|
              M.read (| M.alloc (Binary.modulo (|
                M.read (| M.alloc (Value.Integer IntegerKind.U32 27) |),
                M.read (| BYTES_PER_CHUNK |)
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
                  M.read (| BYTES_PER_CHUNK |),
                  fun (j : Value.t) =>
                  do~ [[
                    M.alloc (M.assign (|
                      M.read (| M.alloc (slice) |),
                      M.read (| M.alloc (Binary.multiply (|
                        M.read (| slice |),
                        M.read (| M.alloc (Value.Integer IntegerKind.Field 256) |)
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
                            M.read (| input |),
                            M.read (| M.alloc (Binary.add (|
                              M.read (| M.alloc (Binary.multiply (|
                                M.read (| i |),
                                M.read (| BYTES_PER_CHUNK |)
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
              let~ slice_base64_chunks := [[ M.copy (|
                M.alloc (M.call_closure (|
                  M.read (| M.get_function (| "to_be_radix", 3 |) |),
                  [
                    M.read (| slice |);
                    M.read (| M.alloc (Value.Integer IntegerKind.U32 64) |)
                  ]
                |))
              |) ]] in
              [[
                M.for_ (|
                  M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
                  M.read (| BASE64_ELEMENTS_PER_CHUNK |),
                  fun (j : Value.t) =>
                  [[
                    M.alloc (M.assign (|
                      M.read (| M.alloc (M.index (|
                        M.read (| M.alloc (result) |),
                        M.read (| M.alloc (Binary.add (|
                          M.read (| M.alloc (Binary.multiply (|
                            M.read (| i |),
                            M.read (| BASE64_ELEMENTS_PER_CHUNK |)
                          |)) |),
                          M.read (| j |)
                        |)) |)
                      |)) |),
                      M.read (| M.alloc (M.index (|
                        M.read (| slice_base64_chunks |),
                        M.read (| j |)
                      |)) |)
                    |))
                  ]]
                |)
              ]]
            |)
          ]] in
          let~ bytes_in_final_chunk := [[ M.copy (|
            M.alloc (Binary.subtract (|
              M.read (| M.alloc (Value.Integer IntegerKind.U32 27) |),
              M.read (| M.alloc (Binary.multiply (|
                M.read (| M.alloc (Binary.subtract (|
                  M.read (| num_chunks |),
                  M.read (| M.alloc (Value.Integer IntegerKind.U32 1) |)
                |)) |),
                M.read (| BYTES_PER_CHUNK |)
              |)) |)
            |))
          |) ]] in
          let~ slice := [[ M.copy_mutable (|
            M.alloc (Value.Integer IntegerKind.Field 0)
          |) ]] in
          do~ [[
            M.for_ (|
              M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
              M.read (| bytes_in_final_chunk |),
              fun (j : Value.t) =>
              do~ [[
                M.alloc (M.assign (|
                  M.read (| M.alloc (slice) |),
                  M.read (| M.alloc (Binary.multiply (|
                    M.read (| slice |),
                    M.read (| M.alloc (Value.Integer IntegerKind.Field 256) |)
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
                        M.read (| input |),
                        M.read (| M.alloc (Binary.add (|
                          M.read (| M.alloc (Binary.multiply (|
                            M.read (| M.alloc (Binary.subtract (|
                              M.read (| num_chunks |),
                              M.read (| M.alloc (Value.Integer IntegerKind.U32 1) |)
                            |)) |),
                            M.read (| BYTES_PER_CHUNK |)
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
              M.read (| bytes_in_final_chunk |),
              M.read (| BYTES_PER_CHUNK |),
              fun (_ : Value.t) =>
              [[
                M.alloc (M.assign (|
                  M.read (| M.alloc (slice) |),
                  M.read (| M.alloc (Binary.multiply (|
                    M.read (| slice |),
                    M.read (| M.alloc (Value.Integer IntegerKind.Field 256) |)
                  |)) |)
                |))
              ]]
            |)
          ]] in
          let~ slice_base64_chunks := [[ M.copy (|
            M.alloc (M.call_closure (|
              M.read (| M.get_function (| "to_be_radix", 3 |) |),
              [
                M.read (| slice |);
                M.read (| M.alloc (Value.Integer IntegerKind.U32 64) |)
              ]
            |))
          |) ]] in
          let~ num_elements_in_final_chunk := [[ M.copy (|
            M.alloc (Binary.subtract (|
              M.read (| M.alloc (Value.Integer IntegerKind.U32 36) |),
              M.read (| M.alloc (Binary.multiply (|
                M.read (| M.alloc (Binary.subtract (|
                  M.read (| num_chunks |),
                  M.read (| M.alloc (Value.Integer IntegerKind.U32 1) |)
                |)) |),
                M.read (| BASE64_ELEMENTS_PER_CHUNK |)
              |)) |)
            |))
          |) ]] in
          do~ [[
            M.for_ (|
              M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
              M.read (| num_elements_in_final_chunk |),
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
                        M.read (| BASE64_ELEMENTS_PER_CHUNK |)
                      |)) |),
                      M.read (| i |)
                    |)) |)
                  |)) |),
                  M.read (| M.alloc (M.index (|
                    M.read (| slice_base64_chunks |),
                    M.read (| i |)
                  |)) |)
                |))
              ]]
            |)
          ]] in
          [[
            M.alloc (M.assign (|
              M.read (| M.alloc (result) |),
              M.read (| M.alloc (M.call_closure (|
                M.read (| M.get_function (| "base64_encode_elements", 4 |) |),
                [
                  M.read (| result |)
                ]
              |)) |)
            |))
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
  fn eq$f2(self$l20: [u8; 36], other$l21: [u8; 36]) -> bool {
      let result$22 = true;
      for i$23 in 0 .. len$array_len(self$l20) {
          result$l22 = (result$l22 & eq$f5(self$l20[i$l23], other$l21[i$l23]))
      };
      result$l22
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
  fn to_be_radix$f3(self$l24: Field, radix$l25: u32) -> [u8; 40] {
      assert_constant$assert_constant(radix$l25);;
      __to_be_radix$to_be_radix(self$l24, radix$l25)
  }
*)
Definition to_be_radix₃ (α : list Value.t) : M.t :=
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

(*
  fn base64_encode_elements$f4(input$l26: [u8; 36]) -> [u8; 36] {
      let Base64Encoder$27 = new$f6();
      let result$28 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
      for i$29 in 0 .. 36 {
          result$l28[i$l29] = get$f7(Base64Encoder$l27, (input$l26[i$l29] as Field))
      };
      result$l28
  }
*)
Definition base64_encode_elements₄ (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let input := M.alloc input in
    let* result :=
      let~ Base64Encoder := [[ M.copy_mutable (|
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
          M.read (| M.alloc (Value.Integer IntegerKind.U8 0) |)
        ])
      |) ]] in
      do~ [[
        M.for_ (|
          M.read (| M.alloc (Value.Integer IntegerKind.U32 0) |),
          M.read (| M.alloc (Value.Integer IntegerKind.U32 36) |),
          fun (i : Value.t) =>
          [[
            M.alloc (M.assign (|
              M.read (| M.alloc (M.index (|
                M.read (| M.alloc (result) |),
                M.read (| i |)
              |)) |),
              M.read (| M.alloc (M.call_closure (|
                M.read (| M.get_function (| "get", 7 |) |),
                [
                  M.read (| Base64Encoder |);
                  M.read (| M.alloc (M.cast (|
                    M.read (| M.alloc (M.index (|
                      M.read (| input |),
                      M.read (| i |)
                    |)) |),
                    IntegerKind.Field
                  |)) |)
                ]
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
  fn eq$f5(self$l30: u8, other$l31: u8) -> bool {
      (self$l30 == other$l31)
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
  fn new$f6() -> ([u8; 64]) {
      {
          let table$32 = [65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 2⁴×5, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 2⁴×7, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 2⁴×3, 49, 50, 51, 52, 53, 54, 55, 56, 57, 43, 47];
          (table$l32)
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
            M.read (| M.alloc (Value.Integer IntegerKind.U8 65) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 66) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 67) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 68) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 69) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 70) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 71) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 72) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 73) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 74) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 75) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 76) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 77) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 78) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 79) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 80) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 81) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 82) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 83) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 84) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 85) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 86) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 87) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 88) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 89) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 90) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 97) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 98) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 99) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 100) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 101) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 102) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 103) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 104) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 105) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 106) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 107) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 108) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 109) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 110) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 111) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 112) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 113) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 114) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 115) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 116) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 117) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 118) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 119) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 120) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 121) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 122) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 48) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 49) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 50) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 51) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 52) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 53) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 54) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 55) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 56) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 57) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 43) |);
            M.read (| M.alloc (Value.Integer IntegerKind.U8 47) |)
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
  fn get$f7(self$l33: ([u8; 64]), idx$l34: Field) -> u8 {
      self$l33.0[idx$l34]
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
