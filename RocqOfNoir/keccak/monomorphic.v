Require Import RocqOfNoir.RocqOfNoir.

(*
  fn to_le_radix$f5(self$l39: Field, radix$l40: u32) -> [u8; 8] {
      if (!is_unconstrained$is_unconstrained()) {
          assert_constant$assert_constant(radix$l40);
      };
      __to_le_radix$to_le_radix(self$l39, radix$l40)
  }
*)
Definition to_le_radix₀ (α : list Value.t) : M.t :=
  match α with
  | [self; radix] =>
    let self := M.alloc self in
    let radix := M.alloc radix in
    let* result :=
      do~ [[
        M.if_ (|
          Unary.not (|
            M.call_closure (|
              M.read (| Builtin.is_unconstrained |),
              []
            |)
          |),
          [[
            M.alloc (M.call_closure (|
              M.read (| Builtin.assert_constant |),
              [
                M.read (| radix |)
              ]
            |))
          ]],
          None
        |)
      ]] in
      [[
        M.alloc (M.call_closure (|
          M.read (| Builtin.__to_le_radix |),
          [
            M.read (| self |);
            M.read (| radix |)
          ]
        |))
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_to_le_radix₀ :
  get_function "to_le_radix" 0 =
  closure to_le_radix₀.
Global Hint Rewrite get_function_to_le_radix₀ : get_function.

(*
  fn eq$f4(self$l37: u8, other$l38: u8) -> bool {
      (self$l37 == other$l38)
  }
*)
Definition eq₀ (α : list Value.t) : M.t :=
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

Axiom get_function_eq₀ :
  get_function "eq" 0 =
  closure eq₀.
Global Hint Rewrite get_function_eq₀ : get_function.

(*
  fn to_le_bytes$f3(self$l32: Field) -> [u8; 8] {
      let bytes$33 = to_le_radix$f5(self$l32, 256);
      if (!is_unconstrained$is_unconstrained()) {
          let p$34 = &[1, 0, 0, 240, 147, 245, 225, 67, 145, 112, 185, 121, 72, 232, 51, 40, 93, 88, 129, 129, 182, 69, 80, 184, 41, 160, 49, 225, 114, 78, 100, 48];
          constrain (len$array_len(bytes$l33) <= len$array_len(p$l34));
          let ok$35 = (len$array_len(bytes$l33) != len$array_len(p$l34));
          for i$36 in 0 .. 8 {
              if (!ok$l35) {
                  if (bytes$l33[((8 - 1) - i$l36)] != p$l34[((8 - 1) - i$l36)]) {
                      constrain (bytes$l33[((8 - 1) - i$l36)] < p$l34[((8 - 1) - i$l36)]);
                      ok$l35 = true
                  }
              }
          };
          constrain ok$l35
      };
      bytes$l33
  }
*)
Definition to_le_bytes₀ (α : list Value.t) : M.t :=
  match α with
  | [self] =>
    let self := M.alloc self in
    let* result :=
      let~ bytes := [[ M.copy (|
        M.alloc (M.call_closure (|
          get_function "to_le_radix" 0,
          [
            M.read (| self |);
            Value.Integer IntegerKind.U32 256
          ]
        |))
      |) ]] in
      do~ [[
        M.if_ (|
          Unary.not (|
            M.call_closure (|
              M.read (| Builtin.is_unconstrained |),
              []
            |)
          |),
          let~ p := [[ M.copy (|
            M.alloc (Value.Slice [
              Value.Integer IntegerKind.U8 1;
              Value.Integer IntegerKind.U8 0;
              Value.Integer IntegerKind.U8 0;
              Value.Integer IntegerKind.U8 240;
              Value.Integer IntegerKind.U8 147;
              Value.Integer IntegerKind.U8 245;
              Value.Integer IntegerKind.U8 225;
              Value.Integer IntegerKind.U8 67;
              Value.Integer IntegerKind.U8 145;
              Value.Integer IntegerKind.U8 112;
              Value.Integer IntegerKind.U8 185;
              Value.Integer IntegerKind.U8 121;
              Value.Integer IntegerKind.U8 72;
              Value.Integer IntegerKind.U8 232;
              Value.Integer IntegerKind.U8 51;
              Value.Integer IntegerKind.U8 40;
              Value.Integer IntegerKind.U8 93;
              Value.Integer IntegerKind.U8 88;
              Value.Integer IntegerKind.U8 129;
              Value.Integer IntegerKind.U8 129;
              Value.Integer IntegerKind.U8 182;
              Value.Integer IntegerKind.U8 69;
              Value.Integer IntegerKind.U8 80;
              Value.Integer IntegerKind.U8 184;
              Value.Integer IntegerKind.U8 41;
              Value.Integer IntegerKind.U8 160;
              Value.Integer IntegerKind.U8 49;
              Value.Integer IntegerKind.U8 225;
              Value.Integer IntegerKind.U8 114;
              Value.Integer IntegerKind.U8 78;
              Value.Integer IntegerKind.U8 100;
              Value.Integer IntegerKind.U8 48
            ])
          |) ]] in
          do~ [[
            M.alloc (M.assert (|
              Binary.less_equal (|
                M.call_closure (|
                  M.read (| Builtin.len |),
                  [
                    M.read (| bytes |)
                  ]
                |),
                M.call_closure (|
                  M.read (| Builtin.len |),
                  [
                    M.read (| p |)
                  ]
                |)
              |),
              None
            |))
          ]] in
          let~ ok := [[ M.copy_mutable (|
            M.alloc (Binary.not_equal (|
              M.call_closure (|
                M.read (| Builtin.len |),
                [
                  M.read (| bytes |)
                ]
              |),
              M.call_closure (|
                M.read (| Builtin.len |),
                [
                  M.read (| p |)
                ]
              |)
            |))
          |) ]] in
          do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              Value.Integer IntegerKind.U32 8,
              fun (i : Value.t) =>
              [[
                M.if_ (|
                  Unary.not (|
                    M.read (| ok |)
                  |),
                  [[
                    M.if_ (|
                      Binary.not_equal (|
                        M.read (| M.index (|
                          bytes,
                          Binary.subtract (|
                            Binary.subtract (|
                              Value.Integer IntegerKind.U32 8,
                              Value.Integer IntegerKind.U32 1
                            |),
                            M.read (| i |)
                          |)
                        |) |),
                        M.read (| M.index (|
                          p,
                          Binary.subtract (|
                            Binary.subtract (|
                              Value.Integer IntegerKind.U32 8,
                              Value.Integer IntegerKind.U32 1
                            |),
                            M.read (| i |)
                          |)
                        |) |)
                      |),
                      do~ [[
                        M.alloc (M.assert (|
                          Binary.less (|
                            M.read (| M.index (|
                              bytes,
                              Binary.subtract (|
                                Binary.subtract (|
                                  Value.Integer IntegerKind.U32 8,
                                  Value.Integer IntegerKind.U32 1
                                |),
                                M.read (| i |)
                              |)
                            |) |),
                            M.read (| M.index (|
                              p,
                              Binary.subtract (|
                                Binary.subtract (|
                                  Value.Integer IntegerKind.U32 8,
                                  Value.Integer IntegerKind.U32 1
                                |),
                                M.read (| i |)
                              |)
                            |) |)
                          |),
                          None
                        |))
                      ]] in
                      [[
                        M.alloc (M.write (|
                          ok,
                          Value.Bool true
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

Axiom get_function_to_le_bytes₀ :
  get_function "to_le_bytes" 0 =
  closure to_le_bytes₀.
Global Hint Rewrite get_function_to_le_bytes₀ : get_function.

(*
  fn eq$f2(self$l28: [u8; 32], other$l29: [u8; 32]) -> bool {
      let result$30 = true;
      for i$31 in 0 .. len$array_len(self$l28) {
          result$l30 = (result$l30 & eq$f4(self$l28[i$l31], other$l29[i$l31]))
      };
      result$l30
  }
*)
Definition eq₁ (α : list Value.t) : M.t :=
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
          Value.Integer IntegerKind.U32 0,
          M.call_closure (|
            M.read (| Builtin.len |),
            [
              M.read (| self |)
            ]
          |),
          fun (i : Value.t) =>
          [[
            M.alloc (M.write (|
              result,
              Binary.and_ (|
                M.read (| result |),
                M.call_closure (|
                  get_function "eq" 0,
                  [
                    M.read (| M.index (|
                      self,
                      M.read (| i |)
                    |) |);
                    M.read (| M.index (|
                      other,
                      M.read (| i |)
                    |) |)
                  ]
                |)
              |)
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

Axiom get_function_eq₁ :
  get_function "eq" 1 =
  closure eq₁.
Global Hint Rewrite get_function_eq₁ : get_function.

(*
  fn keccak256$f1(input$l2: [u8; 1], message_size$l3: u32) -> [u8; 32] {
      constrain (1 >= message_size$l3);
      let block_bytes$4 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
      if is_unconstrained$is_unconstrained() {
          for i$5 in 0 .. message_size$l3 {
              block_bytes$l4[i$l5] = input$l2[i$l5]
          }
      } else {
          for i$6 in 0 .. 1 {
              if (i$l6 < message_size$l3) {
                  block_bytes$l4[i$l6] = input$l2[i$l6]
              }
          }
      };
      let max_blocks$7 = ((1 + BLOCK_SIZE_IN_BYTES$g0) / BLOCK_SIZE_IN_BYTES$g0);
      let real_max_blocks$8 = ((message_size$l3 + BLOCK_SIZE_IN_BYTES$g0) / BLOCK_SIZE_IN_BYTES$g0);
      let real_blocks_bytes$9 = (real_max_blocks$l8 * BLOCK_SIZE_IN_BYTES$g0);
      block_bytes$l4[message_size$l3] = 1;
      block_bytes$l4[(real_blocks_bytes$l9 - 1)] = 128;
      let sliced_buffer$10 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
      for i$11 in 0 .. len$array_len(sliced_buffer$l10) {
          let limb_start$12 = (WORD_SIZE$g1 * i$l11);
          let sliced$13 = 0;
          let v$14 = 1;
          for k$15 in 0 .. WORD_SIZE$g1 {
              sliced$l13 = (sliced$l13 + (v$l14 * (block_bytes$l4[(limb_start$l12 + k$l15)] as Field)));
              v$l14 = (v$l14 * 256)
          };
          sliced_buffer$l10[i$l11] = (sliced$l13 as u64)
      };
      let state$16 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
      if is_unconstrained$is_unconstrained() {
          for i$17 in 0 .. real_max_blocks$l8 {
              if (i$l17 == 0) {
                  for j$18 in 0 .. LIMBS_PER_BLOCK$g2 {
                      state$l16[j$l18] = sliced_buffer$l10[j$l18]
                  }
              } else {
                  for j$19 in 0 .. LIMBS_PER_BLOCK$g2 {
                      state$l16[j$l19] = (state$l16[j$l19] ^ sliced_buffer$l10[((i$l17 * LIMBS_PER_BLOCK$g2) + j$l19)])
                  }
              };
              state$l16 = keccakf1600$keccakf1600(state$l16)
          }
      } else {
          for j$20 in 0 .. LIMBS_PER_BLOCK$g2 {
              state$l16[j$l20] = sliced_buffer$l10[j$l20]
          };
          state$l16 = keccakf1600$keccakf1600(state$l16);
          for i$21 in 1 .. max_blocks$l7 {
              if (i$l21 < real_max_blocks$l8) {
                  for j$22 in 0 .. LIMBS_PER_BLOCK$g2 {
                      state$l16[j$l22] = (state$l16[j$l22] ^ sliced_buffer$l10[((i$l21 * LIMBS_PER_BLOCK$g2) + j$l22)])
                  };
                  state$l16 = keccakf1600$keccakf1600(state$l16)
              }
          }
      };
      let result$23 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
      for i$24 in 0 .. 4 {
          let lane$25 = (state$l16[i$l24] as Field);
          let lane_le$26 = to_le_bytes$f3(lane$l25);
          for j$27 in 0 .. 8 {
              result$l23[((8 * i$l24) + j$l27)] = lane_le$l26[j$l27]
          }
      };
      result$l23
  }
*)
Definition keccak256₀ (α : list Value.t) : M.t :=
  match α with
  | [input; message_size] =>
    let input := M.alloc input in
    let message_size := M.alloc message_size in
    let* result :=
      do~ [[
        M.alloc (M.assert (|
          Binary.greater_equal (|
            Value.Integer IntegerKind.U32 1,
            M.read (| message_size |)
          |),
          None
        |))
      ]] in
      let~ block_bytes := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0
        ])
      |) ]] in
      do~ [[
        M.if_ (|
          M.call_closure (|
            M.read (| Builtin.is_unconstrained |),
            []
          |),
          [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              M.read (| message_size |),
              fun (i : Value.t) =>
              [[
                M.alloc (M.write (|
                  M.index (|
                    block_bytes,
                    M.read (| i |)
                  |),
                  M.read (| M.index (|
                    input,
                    M.read (| i |)
                  |) |)
                |))
              ]]
            |)
          ]],
          (Some ([[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              Value.Integer IntegerKind.U32 1,
              fun (i : Value.t) =>
              [[
                M.if_ (|
                  Binary.less (|
                    M.read (| i |),
                    M.read (| message_size |)
                  |),
                  [[
                    M.alloc (M.write (|
                      M.index (|
                        block_bytes,
                        M.read (| i |)
                      |),
                      M.read (| M.index (|
                        input,
                        M.read (| i |)
                      |) |)
                    |))
                  ]],
                  None
                |)
              ]]
            |)
          ]]))
        |)
      ]] in
      let~ max_blocks := [[ M.copy (|
        M.alloc (Binary.divide (|
          Binary.add (|
            Value.Integer IntegerKind.U32 1,
            get_global "BLOCK_SIZE_IN_BYTES" 0
          |),
          get_global "BLOCK_SIZE_IN_BYTES" 0
        |))
      |) ]] in
      let~ real_max_blocks := [[ M.copy (|
        M.alloc (Binary.divide (|
          Binary.add (|
            M.read (| message_size |),
            get_global "BLOCK_SIZE_IN_BYTES" 0
          |),
          get_global "BLOCK_SIZE_IN_BYTES" 0
        |))
      |) ]] in
      let~ real_blocks_bytes := [[ M.copy (|
        M.alloc (Binary.multiply (|
          M.read (| real_max_blocks |),
          get_global "BLOCK_SIZE_IN_BYTES" 0
        |))
      |) ]] in
      do~ [[
        M.alloc (M.write (|
          M.index (|
            block_bytes,
            M.read (| message_size |)
          |),
          Value.Integer IntegerKind.U8 1
        |))
      ]] in
      do~ [[
        M.alloc (M.write (|
          M.index (|
            block_bytes,
            Binary.subtract (|
              M.read (| real_blocks_bytes |),
              Value.Integer IntegerKind.U32 1
            |)
          |),
          Value.Integer IntegerKind.U8 128
        |))
      ]] in
      let~ sliced_buffer := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0
        ])
      |) ]] in
      do~ [[
        M.for_ (|
          Value.Integer IntegerKind.U32 0,
          M.call_closure (|
            M.read (| Builtin.len |),
            [
              M.read (| sliced_buffer |)
            ]
          |),
          fun (i : Value.t) =>
          let~ limb_start := [[ M.copy (|
            M.alloc (Binary.multiply (|
              get_global "WORD_SIZE" 1,
              M.read (| i |)
            |))
          |) ]] in
          let~ sliced := [[ M.copy_mutable (|
            M.alloc (Value.Integer IntegerKind.Field 0)
          |) ]] in
          let~ v := [[ M.copy_mutable (|
            M.alloc (Value.Integer IntegerKind.Field 1)
          |) ]] in
          do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              get_global "WORD_SIZE" 1,
              fun (k : Value.t) =>
              do~ [[
                M.alloc (M.write (|
                  sliced,
                  Binary.add (|
                    M.read (| sliced |),
                    Binary.multiply (|
                      M.read (| v |),
                      M.cast (|
                        M.read (| M.index (|
                          block_bytes,
                          Binary.add (|
                            M.read (| limb_start |),
                            M.read (| k |)
                          |)
                        |) |),
                        IntegerKind.Field
                      |)
                    |)
                  |)
                |))
              ]] in
              [[
                M.alloc (M.write (|
                  v,
                  Binary.multiply (|
                    M.read (| v |),
                    Value.Integer IntegerKind.Field 256
                  |)
                |))
              ]]
            |)
          ]] in
          [[
            M.alloc (M.write (|
              M.index (|
                sliced_buffer,
                M.read (| i |)
              |),
              M.cast (|
                M.read (| sliced |),
                IntegerKind.U64
              |)
            |))
          ]]
        |)
      ]] in
      let~ state := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0;
          Value.Integer IntegerKind.U64 0
        ])
      |) ]] in
      do~ [[
        M.if_ (|
          M.call_closure (|
            M.read (| Builtin.is_unconstrained |),
            []
          |),
          [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              M.read (| real_max_blocks |),
              fun (i : Value.t) =>
              do~ [[
                M.if_ (|
                  Binary.equal (|
                    M.read (| i |),
                    Value.Integer IntegerKind.U32 0
                  |),
                  [[
                    M.for_ (|
                      Value.Integer IntegerKind.U32 0,
                      get_global "LIMBS_PER_BLOCK" 2,
                      fun (j : Value.t) =>
                      [[
                        M.alloc (M.write (|
                          M.index (|
                            state,
                            M.read (| j |)
                          |),
                          M.read (| M.index (|
                            sliced_buffer,
                            M.read (| j |)
                          |) |)
                        |))
                      ]]
                    |)
                  ]],
                  (Some ([[
                    M.for_ (|
                      Value.Integer IntegerKind.U32 0,
                      get_global "LIMBS_PER_BLOCK" 2,
                      fun (j : Value.t) =>
                      [[
                        M.alloc (M.write (|
                          M.index (|
                            state,
                            M.read (| j |)
                          |),
                          Binary.xor (|
                            M.read (| M.index (|
                              state,
                              M.read (| j |)
                            |) |),
                            M.read (| M.index (|
                              sliced_buffer,
                              Binary.add (|
                                Binary.multiply (|
                                  M.read (| i |),
                                  get_global "LIMBS_PER_BLOCK" 2
                                |),
                                M.read (| j |)
                              |)
                            |) |)
                          |)
                        |))
                      ]]
                    |)
                  ]]))
                |)
              ]] in
              [[
                M.alloc (M.write (|
                  state,
                  M.call_closure (|
                    get_low_level "keccakf1600",
                    [
                      M.read (| state |)
                    ]
                  |)
                |))
              ]]
            |)
          ]],
          (Some (do~ [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              get_global "LIMBS_PER_BLOCK" 2,
              fun (j : Value.t) =>
              [[
                M.alloc (M.write (|
                  M.index (|
                    state,
                    M.read (| j |)
                  |),
                  M.read (| M.index (|
                    sliced_buffer,
                    M.read (| j |)
                  |) |)
                |))
              ]]
            |)
          ]] in
          do~ [[
            M.alloc (M.write (|
              state,
              M.call_closure (|
                get_low_level "keccakf1600",
                [
                  M.read (| state |)
                ]
              |)
            |))
          ]] in
          [[
            M.for_ (|
              Value.Integer IntegerKind.U32 1,
              M.read (| max_blocks |),
              fun (i : Value.t) =>
              [[
                M.if_ (|
                  Binary.less (|
                    M.read (| i |),
                    M.read (| real_max_blocks |)
                  |),
                  do~ [[
                    M.for_ (|
                      Value.Integer IntegerKind.U32 0,
                      get_global "LIMBS_PER_BLOCK" 2,
                      fun (j : Value.t) =>
                      [[
                        M.alloc (M.write (|
                          M.index (|
                            state,
                            M.read (| j |)
                          |),
                          Binary.xor (|
                            M.read (| M.index (|
                              state,
                              M.read (| j |)
                            |) |),
                            M.read (| M.index (|
                              sliced_buffer,
                              Binary.add (|
                                Binary.multiply (|
                                  M.read (| i |),
                                  get_global "LIMBS_PER_BLOCK" 2
                                |),
                                M.read (| j |)
                              |)
                            |) |)
                          |)
                        |))
                      ]]
                    |)
                  ]] in
                  [[
                    M.alloc (M.write (|
                      state,
                      M.call_closure (|
                        get_low_level "keccakf1600",
                        [
                          M.read (| state |)
                        ]
                      |)
                    |))
                  ]],
                  None
                |)
              ]]
            |)
          ]]))
        |)
      ]] in
      let~ result := [[ M.copy_mutable (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0;
          Value.Integer IntegerKind.U8 0
        ])
      |) ]] in
      do~ [[
        M.for_ (|
          Value.Integer IntegerKind.U32 0,
          Value.Integer IntegerKind.U32 4,
          fun (i : Value.t) =>
          let~ lane := [[ M.copy (|
            M.alloc (M.cast (|
              M.read (| M.index (|
                state,
                M.read (| i |)
              |) |),
              IntegerKind.Field
            |))
          |) ]] in
          let~ lane_le := [[ M.copy (|
            M.alloc (M.call_closure (|
              get_function "to_le_bytes" 0,
              [
                M.read (| lane |)
              ]
            |))
          |) ]] in
          [[
            M.for_ (|
              Value.Integer IntegerKind.U32 0,
              Value.Integer IntegerKind.U32 8,
              fun (j : Value.t) =>
              [[
                M.alloc (M.write (|
                  M.index (|
                    result,
                    Binary.add (|
                      Binary.multiply (|
                        Value.Integer IntegerKind.U32 8,
                        M.read (| i |)
                      |),
                      M.read (| j |)
                    |)
                  |),
                  M.read (| M.index (|
                    lane_le,
                    M.read (| j |)
                  |) |)
                |))
              ]]
            |)
          ]]
        |)
      ]] in
      [[
        result
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_keccak256₀ :
  get_function "keccak256" 0 =
  closure keccak256₀.
Global Hint Rewrite get_function_keccak256₀ : get_function.

(*
  fn smoke_test$f0() -> () {
      let input$0 = [189];
      let result$1 = [90, 80, 47, 159, 202, 70, 123, 38, 109, 91, 120, 51, 101, 25, 55, 232, 5, 39, 12, 163, 243, 175, 28, 13, 210, 70, 45, 202, 75, 59, 26, 191];
      constrain eq$f2(keccak256$f1(input$l0, len$array_len(input$l0)), result$l1)
  }
*)
Definition smoke_test₀ (α : list Value.t) : M.t :=
  match α with
  | [] =>
    let* result :=
      let~ input := [[ M.copy (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U8 189
        ])
      |) ]] in
      let~ result := [[ M.copy (|
        M.alloc (Value.Array [
          Value.Integer IntegerKind.U8 90;
          Value.Integer IntegerKind.U8 80;
          Value.Integer IntegerKind.U8 47;
          Value.Integer IntegerKind.U8 159;
          Value.Integer IntegerKind.U8 202;
          Value.Integer IntegerKind.U8 70;
          Value.Integer IntegerKind.U8 123;
          Value.Integer IntegerKind.U8 38;
          Value.Integer IntegerKind.U8 109;
          Value.Integer IntegerKind.U8 91;
          Value.Integer IntegerKind.U8 120;
          Value.Integer IntegerKind.U8 51;
          Value.Integer IntegerKind.U8 101;
          Value.Integer IntegerKind.U8 25;
          Value.Integer IntegerKind.U8 55;
          Value.Integer IntegerKind.U8 232;
          Value.Integer IntegerKind.U8 5;
          Value.Integer IntegerKind.U8 39;
          Value.Integer IntegerKind.U8 12;
          Value.Integer IntegerKind.U8 163;
          Value.Integer IntegerKind.U8 243;
          Value.Integer IntegerKind.U8 175;
          Value.Integer IntegerKind.U8 28;
          Value.Integer IntegerKind.U8 13;
          Value.Integer IntegerKind.U8 210;
          Value.Integer IntegerKind.U8 70;
          Value.Integer IntegerKind.U8 45;
          Value.Integer IntegerKind.U8 202;
          Value.Integer IntegerKind.U8 75;
          Value.Integer IntegerKind.U8 59;
          Value.Integer IntegerKind.U8 26;
          Value.Integer IntegerKind.U8 191
        ])
      |) ]] in
      [[
        M.alloc (M.assert (|
          M.call_closure (|
            get_function "eq" 1,
            [
              M.call_closure (|
                get_function "keccak256" 0,
                [
                  M.read (| input |);
                  M.call_closure (|
                    M.read (| Builtin.len |),
                    [
                      M.read (| input |)
                    ]
                  |)
                ]
              |);
              M.read (| result |)
            ]
          |),
          None
        |))
      ]] in
    M.read result
  | _ => M.impossible "wrong number of arguments"
  end.

Axiom get_function_smoke_test₀ :
  get_function "smoke_test" 0 =
  closure smoke_test₀.
Global Hint Rewrite get_function_smoke_test₀ : get_function.
