Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Require Import Coq.ZArith.Znumtheory.
Require Import Coq.Bool.Bool.

Open Scope Z_scope.

Fixpoint prime_length (s : string) : bool :=
  let n := Z.of_nat (String.length s) in
  if Z.ltb n 2 then false
  else
    let fix is_prime (d : Z) : bool :=
      if Z.ltb d 2 then true
      else if Z.eqb d n then is_prime (d - 1)
           else if Z.eqb (n mod d) 0 then false
                else is_prime (d - 1)
    in is_prime (n - 1).

Lemma prime_5 : prime 5.
Proof.
  apply prime_intro.
  - unfold gt, lt. lia.
  - intros n (H1 & H2).
    assert (H3: n > 0) by lia.
    assert (H4: n <= 5) by lia.
    destruct n as [| [| [| [| [| n]]]]]; try lia.
    + exists 1; lia.
    + exists 1; lia.
    + exists 1; lia.
    + exists 1; lia.
    + exists 5; lia.
Qed.

Example prime_length_example : prime_length "Hello" = true.
Proof.
  unfold prime_length.
  simpl.
  assert (H: prime 5) by apply prime_5.
  reflexivity.
Qed.