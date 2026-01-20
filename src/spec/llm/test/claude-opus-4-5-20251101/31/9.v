Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Require Import Lia.

Open Scope Z_scope.

Definition is_prime_spec (n : Z) (result : bool) : Prop :=
  (n <= 1 -> result = false) /\
  (n > 1 -> 
    (result = true <-> 
      (forall d : Z, 2 <= d -> d < n -> Z.rem n d <> 0))).

Example test_is_prime_17 : is_prime_spec 17 true.
Proof.
  unfold is_prime_spec.
  split.
  - intro H. lia.
  - intro H.
    split.
    + intro Htrue.
      intros d Hd1 Hd2.
      assert (d = 2 \/ d = 3 \/ d = 4 \/ d = 5 \/ d = 6 \/ d = 7 \/ d = 8 \/ 
              d = 9 \/ d = 10 \/ d = 11 \/ d = 12 \/ d = 13 \/ d = 14 \/ 
              d = 15 \/ d = 16) as Hcases by lia.
      destruct Hcases as [H2|[H3|[H4|[H5|[H6|[H7|[H8|[H9|[H10|[H11|[H12|[H13|[H14|[H15|H16]]]]]]]]]]]]]];
      subst; compute; discriminate.
    + intro Hdiv.
      reflexivity.
Qed.