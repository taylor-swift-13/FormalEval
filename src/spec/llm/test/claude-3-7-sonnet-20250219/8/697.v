Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Open Scope Z_scope.

Definition sum_product_spec (numbers : list Z) (result_sum result_product : Z) : Prop :=
  result_sum = fold_left Z.add numbers 0 /\
  result_product = fold_left Z.mul numbers 1.

Example test_sum_product_complex_list :
  sum_product_spec
    [1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 0%Z; 1%Z; -6%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 3%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 1%Z; 4%Z; 1%Z;
     1%Z; 1%Z; 1%Z; 1%Z; 1%Z]
    58 0.
Proof.
  unfold sum_product_spec.
  split.
  - simpl.
    (* Compute the sum: sum all elements *)
    (* sum = number of 1's minus 6 plus 0 plus 3 plus 4 *)
    (* Count 1's: total length is 60; outliers are 0, -6, 3, 4 *)
    (* Number of 1's = 60 - 4 = 56 *)
    (* sum = 56*1 + 0 + (-6) + 3 + 4 = 56 - 6 + 3 + 4 = 57 *)
    (* Check carefully: Let's enumerate sum exactly *)
    (* We can fold add term-by-term or verify manually in Coq. *)
    (* Instead of manual arithmetic here, just use ring simplification *)
    reflexivity.
  - simpl.
    (* Product involves 0, so product = 0 *)
    reflexivity.
Qed.