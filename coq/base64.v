Require Import CoqOfNoir.

Definition test_decode_multi_chunks₀ (α : list Value.t) : M.t :=
  match α with
  | [] =>
    let~ input := [[
      Value.Array [
        Value.Integer 86;
        Value.Integer 71;
        Value.Integer 104;
        Value.Integer 108;
        Value.Integer 73;
        Value.Integer 72;
        Value.Integer 70;
        Value.Integer 49;
        Value.Integer 97;
        Value.Integer 87;
        Value.Integer 78;
        Value.Integer 114;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 74;
        Value.Integer 121;
        Value.Integer 98;
        Value.Integer 51;
        Value.Integer 100;
        Value.Integer 117;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 90;
        Value.Integer 118;
        Value.Integer 101;
        Value.Integer 67;
        Value.Integer 66;
        Value.Integer 113;
        Value.Integer 100;
        Value.Integer 87;
        Value.Integer 49;
        Value.Integer 119;
        Value.Integer 99;
        Value.Integer 121;
        Value.Integer 66;
        Value.Integer 118;
        Value.Integer 100;
        Value.Integer 109;
        Value.Integer 86;
        Value.Integer 121;
        Value.Integer 73;
        Value.Integer 72;
        Value.Integer 82;
        Value.Integer 111;
        Value.Integer 90;
        Value.Integer 83;
        Value.Integer 66;
        Value.Integer 115;
        Value.Integer 89;
        Value.Integer 88;
        Value.Integer 112;
        Value.Integer 53;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 82;
        Value.Integer 118;
        Value.Integer 90;
        Value.Integer 121;
        Value.Integer 119;
        Value.Integer 103;
        Value.Integer 100;
        Value.Integer 50;
        Value.Integer 104;
        Value.Integer 112;
        Value.Integer 98;
        Value.Integer 71;
        Value.Integer 85;
        Value.Integer 103;
        Value.Integer 78;
        Value.Integer 68;
        Value.Integer 73;
        Value.Integer 103;
        Value.Integer 99;
        Value.Integer 109;
        Value.Integer 70;
        Value.Integer 50;
        Value.Integer 90;
        Value.Integer 87;
        Value.Integer 53;
        Value.Integer 122;
        Value.Integer 73;
        Value.Integer 72;
        Value.Integer 66;
        Value.Integer 108;
        Value.Integer 99;
        Value.Integer 109;
        Value.Integer 78;
        Value.Integer 111;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 70;
        Value.Integer 48;
        Value.Integer 98;
        Value.Integer 51;
        Value.Integer 65;
        Value.Integer 103;
        Value.Integer 89;
        Value.Integer 83;
        Value.Integer 66;
        Value.Integer 121;
        Value.Integer 100;
        Value.Integer 88;
        Value.Integer 78;
        Value.Integer 48;
        Value.Integer 101;
        Value.Integer 83;
        Value.Integer 66;
        Value.Integer 116;
        Value.Integer 89;
        Value.Integer 87;
        Value.Integer 108;
        Value.Integer 115;
        Value.Integer 89;
        Value.Integer 109;
        Value.Integer 57;
        Value.Integer 52;
        Value.Integer 76;
        Value.Integer 105;
        Value.Integer 66;
        Value.Integer 97;
        Value.Integer 89;
        Value.Integer 87;
        Value.Integer 53;
        Value.Integer 53;
        Value.Integer 73;
        Value.Integer 72;
        Value.Integer 70;
        Value.Integer 49;
        Value.Integer 97;
        Value.Integer 87;
        Value.Integer 120;
        Value.Integer 48;
        Value.Integer 90;
        Value.Integer 88;
        Value.Integer 74;
        Value.Integer 122;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 90;
        Value.Integer 104;
        Value.Integer 89;
        Value.Integer 110;
        Value.Integer 74;
        Value.Integer 112;
        Value.Integer 89;
        Value.Integer 50;
        Value.Integer 70;
        Value.Integer 48;
        Value.Integer 90;
        Value.Integer 83;
        Value.Integer 65;
        Value.Integer 53;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 78;
        Value.Integer 118;
        Value.Integer 101;
        Value.Integer 110;
        Value.Integer 107;
        Value.Integer 103;
        Value.Integer 89;
        Value.Integer 109;
        Value.Integer 120;
        Value.Integer 104;
        Value.Integer 98;
        Value.Integer 109;
        Value.Integer 116;
        Value.Integer 108;
        Value.Integer 100;
        Value.Integer 72;
        Value.Integer 77;
        Value.Integer 115;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 70;
        Value.Integer 122;
        Value.Integer 73;
        Value.Integer 68;
        Value.Integer 77;
        Value.Integer 103;
        Value.Integer 97;
        Value.Integer 109;
        Value.Integer 57;
        Value.Integer 50;
        Value.Integer 97;
        Value.Integer 87;
        Value.Integer 70;
        Value.Integer 115;
        Value.Integer 73;
        Value.Integer 72;
        Value.Integer 100;
        Value.Integer 112;
        Value.Integer 101;
        Value.Integer 109;
        Value.Integer 70;
        Value.Integer 121;
        Value.Integer 90;
        Value.Integer 72;
        Value.Integer 77;
        Value.Integer 103;
        Value.Integer 90;
        Value.Integer 88;
        Value.Integer 104;
        Value.Integer 119;
        Value.Integer 90;
        Value.Integer 88;
        Value.Integer 74;
        Value.Integer 48;
        Value.Integer 98;
        Value.Integer 72;
        Value.Integer 107;
        Value.Integer 103;
        Value.Integer 98;
        Value.Integer 87;
        Value.Integer 108;
        Value.Integer 52;
        Value.Integer 73;
        Value.Integer 68;
        Value.Integer 85;
        Value.Integer 103;
        Value.Integer 99;
        Value.Integer 71;
        Value.Integer 57;
        Value.Integer 48;
        Value.Integer 90;
        Value.Integer 87;
        Value.Integer 53;
        Value.Integer 48;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 86;
        Value.Integer 115;
        Value.Integer 97;
        Value.Integer 88;
        Value.Integer 104;
        Value.Integer 112;
        Value.Integer 99;
        Value.Integer 110;
        Value.Integer 77;
        Value.Integer 117;
        Value.Integer 73;
        Value.Integer 69;
        Value.Integer 74;
        Value.Integer 121;
        Value.Integer 97;
        Value.Integer 87;
        Value.Integer 100;
        Value.Integer 111;
        Value.Integer 100;
        Value.Integer 67;
        Value.Integer 66;
        Value.Integer 117;
        Value.Integer 90;
        Value.Integer 87;
        Value.Integer 57;
        Value.Integer 117;
        Value.Integer 73;
        Value.Integer 72;
        Value.Integer 78;
        Value.Integer 112;
        Value.Integer 90;
        Value.Integer 50;
        Value.Integer 53;
        Value.Integer 122;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 90;
        Value.Integer 115;
        Value.Integer 89;
        Value.Integer 88;
        Value.Integer 78;
        Value.Integer 111;
        Value.Integer 73;
        Value.Integer 67;
        Value.Integer 74;
        Value.Integer 80;
        Value.Integer 85;
        Value.Integer 69;
        Value.Integer 86;
        Value.Integer 79;
        Value.Integer 73;
        Value.Integer 68;
        Value.Integer 73;
        Value.Integer 48;
        Value.Integer 76;
        Value.Integer 122;
        Value.Integer 99;
        Value.Integer 105;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 108;
        Value.Integer 117;
        Value.Integer 73;
        Value.Integer 72;
        Value.Integer 82;
        Value.Integer 111;
        Value.Integer 90;
        Value.Integer 83;
        Value.Integer 66;
        Value.Integer 116;
        Value.Integer 97;
        Value.Integer 88;
        Value.Integer 78;
        Value.Integer 48;
        Value.Integer 101;
        Value.Integer 83;
        Value.Integer 66;
        Value.Integer 117;
        Value.Integer 97;
        Value.Integer 87;
        Value.Integer 100;
        Value.Integer 111;
        Value.Integer 100;
        Value.Integer 67;
        Value.Integer 66;
        Value.Integer 104;
        Value.Integer 97;
        Value.Integer 88;
        Value.Integer 73;
        Value.Integer 115;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 108;
        Value.Integer 115;
        Value.Integer 98;
        Value.Integer 72;
        Value.Integer 86;
        Value.Integer 116;
        Value.Integer 97;
        Value.Integer 87;
        Value.Integer 53;
        Value.Integer 104;
        Value.Integer 100;
        Value.Integer 71;
        Value.Integer 108;
        Value.Integer 117;
        Value.Integer 90;
        Value.Integer 121;
        Value.Integer 65;
        Value.Integer 52;
        Value.Integer 73;
        Value.Integer 72;
        Value.Integer 90;
        Value.Integer 112;
        Value.Integer 98;
        Value.Integer 110;
        Value.Integer 82;
        Value.Integer 104;
        Value.Integer 90;
        Value.Integer 50;
        Value.Integer 85;
        Value.Integer 103;
        Value.Integer 89;
        Value.Integer 50;
        Value.Integer 70;
        Value.Integer 121;
        Value.Integer 99;
        Value.Integer 121;
        Value.Integer 66;
        Value.Integer 119;
        Value.Integer 89;
        Value.Integer 88;
        Value.Integer 74;
        Value.Integer 114;
        Value.Integer 90;
        Value.Integer 87;
        Value.Integer 81;
        Value.Integer 103;
        Value.Integer 89;
        Value.Integer 87;
        Value.Integer 120;
        Value.Integer 118;
        Value.Integer 98;
        Value.Integer 109;
        Value.Integer 99;
        Value.Integer 103;
        Value.Integer 84;
        Value.Integer 87;
        Value.Integer 70;
        Value.Integer 112;
        Value.Integer 98;
        Value.Integer 105;
        Value.Integer 66;
        Value.Integer 84;
        Value.Integer 100;
        Value.Integer 72;
        Value.Integer 74;
        Value.Integer 108;
        Value.Integer 90;
        Value.Integer 88;
        Value.Integer 81;
        Value.Integer 117;
        Value.Integer 73;
        Value.Integer 69;
        Value.Integer 69;
        Value.Integer 103;
        Value.Integer 90;
        Value.Integer 50;
        Value.Integer 86;
        Value.Integer 117;
        Value.Integer 100;
        Value.Integer 71;
        Value.Integer 120;
        Value.Integer 108;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 74;
        Value.Integer 121;
        Value.Integer 90;
        Value.Integer 87;
        Value.Integer 86;
        Value.Integer 54;
        Value.Integer 90;
        Value.Integer 83;
        Value.Integer 66;
        Value.Integer 106;
        Value.Integer 89;
        Value.Integer 88;
        Value.Integer 74;
        Value.Integer 121;
        Value.Integer 97;
        Value.Integer 87;
        Value.Integer 86;
        Value.Integer 122;
        Value.Integer 73;
        Value.Integer 72;
        Value.Integer 82;
        Value.Integer 111;
        Value.Integer 90;
        Value.Integer 83;
        Value.Integer 66;
        Value.Integer 104;
        Value.Integer 99;
        Value.Integer 109;
        Value.Integer 57;
        Value.Integer 116;
        Value.Integer 89;
        Value.Integer 83;
        Value.Integer 66;
        Value.Integer 118;
        Value.Integer 90;
        Value.Integer 105;
        Value.Integer 66;
        Value.Integer 109;
        Value.Integer 99;
        Value.Integer 109;
        Value.Integer 86;
        Value.Integer 122;
        Value.Integer 97;
        Value.Integer 67;
        Value.Integer 66;
        Value.Integer 106;
        Value.Integer 98;
        Value.Integer 50;
        Value.Integer 90;
        Value.Integer 109;
        Value.Integer 90;
        Value.Integer 87;
        Value.Integer 85;
        Value.Integer 103;
        Value.Integer 89;
        Value.Integer 87;
        Value.Integer 53;
        Value.Integer 107;
        Value.Integer 73;
        Value.Integer 72;
        Value.Integer 100;
        Value.Integer 104;
        Value.Integer 99;
        Value.Integer 109;
        Value.Integer 48;
        Value.Integer 103;
        Value.Integer 89;
        Value.Integer 50;
        Value.Integer 108;
        Value.Integer 117;
        Value.Integer 98;
        Value.Integer 109;
        Value.Integer 70;
        Value.Integer 116;
        Value.Integer 98;
        Value.Integer 50;
        Value.Integer 52;
        Value.Integer 103;
        Value.Integer 99;
        Value.Integer 109;
        Value.Integer 57;
        Value.Integer 115;
        Value.Integer 98;
        Value.Integer 72;
        Value.Integer 77;
        Value.Integer 103;
        Value.Integer 90;
        Value.Integer 110;
        Value.Integer 74;
        Value.Integer 118;
        Value.Integer 98;
        Value.Integer 83;
        Value.Integer 66;
        Value.Integer 75;
        Value.Integer 98;
        Value.Integer 50;
        Value.Integer 85;
        Value.Integer 110;
        Value.Integer 99;
        Value.Integer 121;
        Value.Integer 66;
        Value.Integer 69;
        Value.Integer 97;
        Value.Integer 87;
        Value.Integer 53;
        Value.Integer 108;
        Value.Integer 99;
        Value.Integer 105;
        Value.Integer 119;
        Value.Integer 103;
        Value.Integer 90;
        Value.Integer 87;
        Value.Integer 53;
        Value.Integer 48;
        Value.Integer 97;
        Value.Integer 87;
        Value.Integer 78;
        Value.Integer 112;
        Value.Integer 98;
        Value.Integer 109;
        Value.Integer 99;
        Value.Integer 103;
        Value.Integer 78;
        Value.Integer 105;
        Value.Integer 66;
        Value.Integer 122;
        Value.Integer 98;
        Value.Integer 71;
        Value.Integer 86;
        Value.Integer 108;
        Value.Integer 99;
        Value.Integer 72;
        Value.Integer 107;
        Value.Integer 103;
        Value.Integer 100;
        Value.Integer 72;
        Value.Integer 74;
        Value.Integer 49;
        Value.Integer 89;
        Value.Integer 50;
        Value.Integer 116;
        Value.Integer 108;
        Value.Integer 99;
        Value.Integer 110;
        Value.Integer 77;
        Value.Integer 103;
        Value.Integer 100;
        Value.Integer 71;
        Value.Integer 56;
        Value.Integer 103;
        Value.Integer 99;
        Value.Integer 51;
        Value.Integer 82;
        Value.Integer 118;
        Value.Integer 99;
        Value.Integer 67;
        Value.Integer 66;
        Value.Integer 109;
        Value.Integer 98;
        Value.Integer 51;
        Value.Integer 73;
        Value.Integer 103;
        Value.Integer 89;
        Value.Integer 83;
        Value.Integer 66;
        Value.Integer 115;
        Value.Integer 89;
        Value.Integer 88;
        Value.Integer 82;
        Value.Integer 108;
        Value.Integer 76;
        Value.Integer 87;
        Value.Integer 53;
        Value.Integer 112;
        Value.Integer 90;
        Value.Integer 50;
        Value.Integer 104;
        Value.Integer 48;
        Value.Integer 73;
        Value.Integer 72;
        Value.Integer 78;
        Value.Integer 117;
        Value.Integer 89;
        Value.Integer 87;
        Value.Integer 78;
        Value.Integer 114;
        Value.Integer 76;
        Value.Integer 105;
        Value.Integer 66;
        Value.Integer 78;
        Value.Integer 90;
        Value.Integer 87;
        Value.Integer 70;
        Value.Integer 117;
        Value.Integer 100;
        Value.Integer 50;
        Value.Integer 104;
        Value.Integer 112;
        Value.Integer 98;
        Value.Integer 71;
        Value.Integer 85;
        Value.Integer 115;
        Value.Integer 73;
        Value.Integer 68;
        Value.Integer 69;
        Value.Integer 120;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 49;
        Value.Integer 112;
        Value.Integer 99;
        Value.Integer 50;
        Value.Integer 78;
        Value.Integer 111;
        Value.Integer 97;
        Value.Integer 87;
        Value.Integer 86;
        Value.Integer 50;
        Value.Integer 98;
        Value.Integer 51;
        Value.Integer 86;
        Value.Integer 122;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 116;
        Value.Integer 112;
        Value.Integer 100;
        Value.Integer 72;
        Value.Integer 82;
        Value.Integer 108;
        Value.Integer 98;
        Value.Integer 110;
        Value.Integer 77;
        Value.Integer 103;
        Value.Integer 99;
        Value.Integer 71;
        Value.Integer 120;
        Value.Integer 104;
        Value.Integer 101;
        Value.Integer 87;
        Value.Integer 90;
        Value.Integer 49;
        Value.Integer 98;
        Value.Integer 71;
        Value.Integer 120;
        Value.Integer 53;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 78;
        Value.Integer 111;
        Value.Integer 89;
        Value.Integer 88;
        Value.Integer 78;
        Value.Integer 108;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 69;
        Value.Integer 103;
        Value.Integer 89;
        Value.Integer 109;
        Value.Integer 70;
        Value.Integer 115;
        Value.Integer 98;
        Value.Integer 67;
        Value.Integer 66;
        Value.Integer 118;
        Value.Integer 90;
        Value.Integer 105;
        Value.Integer 66;
        Value.Integer 53;
        Value.Integer 89;
        Value.Integer 88;
        Value.Integer 74;
        Value.Integer 117;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 70;
        Value.Integer 106;
        Value.Integer 99;
        Value.Integer 109;
        Value.Integer 57;
        Value.Integer 122;
        Value.Integer 99;
        Value.Integer 121;
        Value.Integer 66;
        Value.Integer 78;
        Value.Integer 99;
        Value.Integer 110;
        Value.Integer 77;
        Value.Integer 117;
        Value.Integer 73;
        Value.Integer 69;
        Value.Integer 112;
        Value.Integer 118;
        Value.Integer 97;
        Value.Integer 71;
        Value.Integer 53;
        Value.Integer 122;
        Value.Integer 98;
        Value.Integer 50;
        Value.Integer 52;
        Value.Integer 110;
        Value.Integer 99;
        Value.Integer 121;
        Value.Integer 66;
        Value.Integer 119;
        Value.Integer 98;
        Value.Integer 51;
        Value.Integer 74;
        Value.Integer 106;
        Value.Integer 97;
        Value.Integer 67;
        Value.Integer 119;
        Value.Integer 103;
        Value.Integer 100;
        Value.Integer 71;
        Value.Integer 104;
        Value.Integer 108;
        Value.Integer 97;
        Value.Integer 88;
        Value.Integer 73;
        Value.Integer 103;
        Value.Integer 89;
        Value.Integer 87;
        Value.Integer 53;
        Value.Integer 48;
        Value.Integer 97;
        Value.Integer 87;
        Value.Integer 78;
        Value.Integer 122;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 57;
        Value.Integer 105;
        Value.Integer 99;
        Value.Integer 50;
        Value.Integer 86;
        Value.Integer 121;
        Value.Integer 100;
        Value.Integer 109;
        Value.Integer 86;
        Value.Integer 107;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 74;
        Value.Integer 53;
        Value.Integer 73;
        Value.Integer 68;
        Value.Integer 73;
        Value.Integer 103;
        Value.Integer 100;
        Value.Integer 50;
        Value.Integer 108;
        Value.Integer 122;
        Value.Integer 90;
        Value.Integer 83;
        Value.Integer 66;
        Value.Integer 118;
        Value.Integer 98;
        Value.Integer 71;
        Value.Integer 81;
        Value.Integer 103;
        Value.Integer 98;
        Value.Integer 51;
        Value.Integer 100;
        Value.Integer 115;
        Value.Integer 99;
        Value.Integer 121;
        Value.Integer 66;
        Value.Integer 119;
        Value.Integer 90;
        Value.Integer 88;
        Value.Integer 74;
        Value.Integer 106;
        Value.Integer 97;
        Value.Integer 71;
        Value.Integer 86;
        Value.Integer 107;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 57;
        Value.Integer 117;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 69;
        Value.Integer 103;
        Value.Integer 98;
        Value.Integer 109;
        Value.Integer 86;
        Value.Integer 104;
        Value.Integer 99;
        Value.Integer 109;
        Value.Integer 74;
        Value.Integer 53;
        Value.Integer 73;
        Value.Integer 71;
        Value.Integer 57;
        Value.Integer 104;
        Value.Integer 97;
        Value.Integer 121;
        Value.Integer 66;
        Value.Integer 48;
        Value.Integer 99;
        Value.Integer 109;
        Value.Integer 86;
        Value.Integer 108;
        Value.Integer 76;
        Value.Integer 103
      ] ]] in
    let~ result := [[
      M.call_closure (|
        M.get_function (| "base64_decode", 1 |),
        [
          input
        ]
      |) ]] in
    let~ expected := [[
      Value.String "The quick brown fox jumps over the lazy dog, while 42 ravens perch atop a rusty mailbox. Zany quilters fabricate 9 cozy blankets, as 3 jovial wizards expertly mix 5 potent elixirs. Bright neon signs flash ""OPEN 24/7"" in the misty night air, illuminating 8 vintage cars parked along Main Street. A gentle breeze carries the aroma of fresh coffee and warm cinnamon rolls from Joe's Diner, enticing 6 sleepy truckers to stop for a late-night snack. Meanwhile, 11 mischievous kittens playfully chase a ball of yarn across Mrs. Johnson's porch, their antics observed by 2 wise old owls perched on a nearby oak tree." ]] in
    [[
      M.assert (|
        M.call_closure (|
          M.get_function (| "eq", 2 |),
          [
            result;
            M.call_closure (|
              Builtin.as_bytes,
              [
                expected
              ]
            |)
          ]
        |),
        None
      |)
    ]]
  | _ => M.impossible "wrong number of arguments"
  end.

Definition base64_decode₁ (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let~ decoded := [[
      M.call_closure (|
        M.get_function (| "base64_decode_elements", 3 |),
        [
          input
        ]
      |) ]] in
    let~ result := [[
      Value.Array [
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0
      ] ]] in
    let~ BASE64_ELEMENTS_PER_CHUNK := [[
      Value.Integer 40 ]] in
    let~ BYTES_PER_CHUNK := [[
      Value.Integer 30 ]] in
    let~ num_chunks := [[
      Binary.add (|
        Binary.divide (|
          Value.Integer 814,
          BASE64_ELEMENTS_PER_CHUNK
        |),
        M.cast (|
          Binary.not_equal (|
            Binary.modulo (|
              Value.Integer 814,
              BASE64_ELEMENTS_PER_CHUNK
            |),
            Value.Integer 0
          |),
          Ty.Integer Ty.Signedness.Unsigned Ty.IntegerBitSize.ThirtyTwo
        |)
      |) ]] in
    do~ [[
      M.if_ (|
        Binary.greater (|
          num_chunks,
          Value.Integer 0
        |),
        do~ [[
          M.for_ (|
            Value.Integer 0,
            Binary.subtract (|
              num_chunks,
              Value.Integer 1
            |),
            fun (i : Value.t) =>
            let~ slice := [[
              Value.Integer 0 ]] in
            do~ [[
              M.for_ (|
                Value.Integer 0,
                BASE64_ELEMENTS_PER_CHUNK,
                fun (j : Value.t) =>
                do~ [[
                  M.assign (|
                    slice,
                    Binary.multiply (|
                      slice,
                      Value.Integer 64
                    |)
                  |)
                ]] in
                [[
                  M.assign (|
                    slice,
                    Binary.add (|
                      slice,
                      M.cast (|
                        M.index (|
                          decoded,
                          Binary.add (|
                            Binary.multiply (|
                              i,
                              BASE64_ELEMENTS_PER_CHUNK
                            |),
                            j
                          |)
                        |),
                        Ty.Field
                      |)
                    |)
                  |)
                ]]
              |)
            ]] in
            let~ slice_bytes := [[
              M.call_closure (|
                M.get_function (| "to_be_bytes", 4 |),
                [
                  slice
                ]
              |) ]] in
            [[
              M.for_ (|
                Value.Integer 0,
                BYTES_PER_CHUNK,
                fun (j : Value.t) =>
                [[
                  M.assign (|
                    M.index (|
                      result,
                      Binary.add (|
                        Binary.multiply (|
                          i,
                          BYTES_PER_CHUNK
                        |),
                        j
                      |)
                    |),
                    M.index (|
                      slice_bytes,
                      j
                    |)
                  |)
                ]]
              |)
            ]]
          |)
        ]] in
        let~ base64_elements_in_final_chunk := [[
          Binary.subtract (|
            Value.Integer 814,
            Binary.multiply (|
              Binary.subtract (|
                num_chunks,
                Value.Integer 1
              |),
              BASE64_ELEMENTS_PER_CHUNK
            |)
          |) ]] in
        let~ slice := [[
          Value.Integer 0 ]] in
        do~ [[
          M.for_ (|
            Value.Integer 0,
            base64_elements_in_final_chunk,
            fun (j : Value.t) =>
            do~ [[
              M.assign (|
                slice,
                Binary.multiply (|
                  slice,
                  Value.Integer 64
                |)
              |)
            ]] in
            [[
              M.assign (|
                slice,
                Binary.add (|
                  slice,
                  M.cast (|
                    M.index (|
                      decoded,
                      Binary.add (|
                        Binary.multiply (|
                          Binary.subtract (|
                            num_chunks,
                            Value.Integer 1
                          |),
                          BASE64_ELEMENTS_PER_CHUNK
                        |),
                        j
                      |)
                    |),
                    Ty.Field
                  |)
                |)
              |)
            ]]
          |)
        ]] in
        do~ [[
          M.for_ (|
            base64_elements_in_final_chunk,
            BASE64_ELEMENTS_PER_CHUNK,
            fun (_ : Value.t) =>
            [[
              M.assign (|
                slice,
                Binary.multiply (|
                  slice,
                  Value.Integer 64
                |)
              |)
            ]]
          |)
        ]] in
        let~ slice_bytes := [[
          M.call_closure (|
            M.get_function (| "to_be_bytes", 4 |),
            [
              slice
            ]
          |) ]] in
        let~ num_bytes_in_final_chunk := [[
          Binary.subtract (|
            Value.Integer 610,
            Binary.multiply (|
              Binary.subtract (|
                num_chunks,
                Value.Integer 1
              |),
              BYTES_PER_CHUNK
            |)
          |) ]] in
        [[
          M.for_ (|
            Value.Integer 0,
            num_bytes_in_final_chunk,
            fun (i : Value.t) =>
            [[
              M.assign (|
                M.index (|
                  result,
                  Binary.add (|
                    Binary.multiply (|
                      Binary.subtract (|
                        num_chunks,
                        Value.Integer 1
                      |),
                      BYTES_PER_CHUNK
                    |),
                    i
                  |)
                |),
                M.index (|
                  slice_bytes,
                  i
                |)
              |)
            ]]
          |)
        ]],
        None
      |)
    ]] in
    [[
      result
    ]]
  | _ => M.impossible "wrong number of arguments"
  end.

Definition eq₂ (α : list Value.t) : M.t :=
  match α with
  | [self; other] =>
    let~ result := [[
      Value.Bool true ]] in
    do~ [[
      M.for_ (|
        Value.Integer 0,
        M.call_closure (|
          Builtin.len,
          [
            self
          ]
        |),
        fun (i : Value.t) =>
        [[
          M.assign (|
            result,
            Binary.and_ (|
              result,
              M.call_closure (|
                M.get_function (| "eq", 5 |),
                [
                  M.index (|
                    self,
                    i
                  |);
                  M.index (|
                    other,
                    i
                  |)
                ]
              |)
            |)
          |)
        ]]
      |)
    ]] in
    [[
      result
    ]]
  | _ => M.impossible "wrong number of arguments"
  end.

Definition base64_decode_elements₃ (α : list Value.t) : M.t :=
  match α with
  | [input] =>
    let~ Base64Decoder := [[
      M.call_closure (|
        M.get_function (| "new", 6 |),
        []
      |) ]] in
    let~ result := [[
      Value.Array [
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0;
        Value.Integer 0
      ] ]] in
    do~ [[
      M.for_ (|
        Value.Integer 0,
        Value.Integer 814,
        fun (i : Value.t) =>
        let~ input_byte := [[
          M.index (|
            input,
            i
          |) ]] in
        do~ [[
          M.assign (|
            M.index (|
              result,
              i
            |),
            M.call_closure (|
              M.get_function (| "get", 7 |),
              [
                Base64Decoder;
                M.cast (|
                  input_byte,
                  Ty.Field
                |)
              ]
            |)
          |)
        ]] in
        [[
          M.assert (|
            Binary.not_equal (|
              M.index (|
                result,
                i
              |),
              Value.Integer 255
            |),
            Some (Value.fmt_str "DecodeError: invalid symbol {input_byte}, offset {i}." 2(Value.Tuple [input_byte; i]))
          |)
        ]]
      |)
    ]] in
    [[
      result
    ]]
  | _ => M.impossible "wrong number of arguments"
  end.

Definition to_be_bytes₄ (α : list Value.t) : M.t :=
  match α with
  | [self] =>
    let~ bytes := [[
      M.call_closure (|
        M.get_function (| "to_be_radix", 8 |),
        [
          self;
          Value.Integer 256
        ]
      |) ]] in
    do~ [[
      M.if_ (|
        Unary.not (|
          M.call_closure (|
            Builtin.is_unconstrained,
            []
          |)
        |),
        let~ p := [[
          Value.Slice [
            Value.Integer 48;
            Value.Integer 100;
            Value.Integer 78;
            Value.Integer 114;
            Value.Integer 225;
            Value.Integer 49;
            Value.Integer 160;
            Value.Integer 41;
            Value.Integer 184;
            Value.Integer 80;
            Value.Integer 69;
            Value.Integer 182;
            Value.Integer 129;
            Value.Integer 129;
            Value.Integer 88;
            Value.Integer 93;
            Value.Integer 40;
            Value.Integer 51;
            Value.Integer 232;
            Value.Integer 72;
            Value.Integer 121;
            Value.Integer 185;
            Value.Integer 112;
            Value.Integer 145;
            Value.Integer 67;
            Value.Integer 225;
            Value.Integer 245;
            Value.Integer 147;
            Value.Integer 240;
            Value.Integer 0;
            Value.Integer 0;
            Value.Integer 1
          ] ]] in
        do~ [[
          M.assert (|
            Binary.less_equal (|
              M.call_closure (|
                Builtin.len,
                [
                  bytes
                ]
              |),
              M.call_closure (|
                Builtin.len,
                [
                  p
                ]
              |)
            |),
            None
          |)
        ]] in
        let~ ok := [[
          Binary.not_equal (|
            M.call_closure (|
              Builtin.len,
              [
                bytes
              ]
            |),
            M.call_closure (|
              Builtin.len,
              [
                p
              ]
            |)
          |) ]] in
        do~ [[
          M.for_ (|
            Value.Integer 0,
            Value.Integer 30,
            fun (i : Value.t) =>
            [[
              M.if_ (|
                Unary.not (|
                  ok
                |),
                [[
                  M.if_ (|
                    Binary.not_equal (|
                      M.index (|
                        bytes,
                        i
                      |),
                      M.index (|
                        p,
                        i
                      |)
                    |),
                    do~ [[
                      M.assert (|
                        Binary.less (|
                          M.index (|
                            bytes,
                            i
                          |),
                          M.index (|
                            p,
                            i
                          |)
                        |),
                        None
                      |)
                    ]] in
                    [[
                      M.assign (|
                        ok,
                        Value.Bool true
                      |)
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
          M.assert (|
            ok,
            None
          |)
        ]],
        None
      |)
    ]] in
    [[
      bytes
    ]]
  | _ => M.impossible "wrong number of arguments"
  end.

Definition eq₅ (α : list Value.t) : M.t :=
  match α with
  | [self; other] =>
    [[
      Binary.equal (|
        self,
        other
      |)
    ]]
  | _ => M.impossible "wrong number of arguments"
  end.

Definition new₆ (α : list Value.t) : M.t :=
  match α with
  | [] =>
    [[
      let~ table := [[
        Value.Array [
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 62;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 63;
          Value.Integer 52;
          Value.Integer 53;
          Value.Integer 54;
          Value.Integer 55;
          Value.Integer 56;
          Value.Integer 57;
          Value.Integer 58;
          Value.Integer 59;
          Value.Integer 60;
          Value.Integer 61;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 0;
          Value.Integer 1;
          Value.Integer 2;
          Value.Integer 3;
          Value.Integer 4;
          Value.Integer 5;
          Value.Integer 6;
          Value.Integer 7;
          Value.Integer 8;
          Value.Integer 9;
          Value.Integer 10;
          Value.Integer 11;
          Value.Integer 12;
          Value.Integer 13;
          Value.Integer 14;
          Value.Integer 15;
          Value.Integer 16;
          Value.Integer 17;
          Value.Integer 18;
          Value.Integer 19;
          Value.Integer 20;
          Value.Integer 21;
          Value.Integer 22;
          Value.Integer 23;
          Value.Integer 24;
          Value.Integer 25;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 26;
          Value.Integer 27;
          Value.Integer 28;
          Value.Integer 29;
          Value.Integer 30;
          Value.Integer 31;
          Value.Integer 32;
          Value.Integer 33;
          Value.Integer 34;
          Value.Integer 35;
          Value.Integer 36;
          Value.Integer 37;
          Value.Integer 38;
          Value.Integer 39;
          Value.Integer 40;
          Value.Integer 41;
          Value.Integer 42;
          Value.Integer 43;
          Value.Integer 44;
          Value.Integer 45;
          Value.Integer 46;
          Value.Integer 47;
          Value.Integer 48;
          Value.Integer 49;
          Value.Integer 50;
          Value.Integer 51;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255;
          Value.Integer 255
        ] ]] in
      [[
        Value.Tuple [table]
      ]]
    ]]
  | _ => M.impossible "wrong number of arguments"
  end.

Definition get₇ (α : list Value.t) : M.t :=
  match α with
  | [self; idx] =>
    [[
      M.index (|
        M.extract_tuple_field (|
          self,
          0
        |),
        idx
      |)
    ]]
  | _ => M.impossible "wrong number of arguments"
  end.

Definition to_be_radix₈ (α : list Value.t) : M.t :=
  match α with
  | [self; radix] =>
    do~ [[
      M.call_closure (|
        Builtin.assert_constant,
        [
          radix
        ]
      |)
    ]] in
    [[
      M.call_closure (|
        Builtin.__to_be_radix,
        [
          self;
          radix
        ]
      |)
    ]]
  | _ => M.impossible "wrong number of arguments"
  end.
