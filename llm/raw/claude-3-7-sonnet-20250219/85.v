
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition add_spec (lst : list Z) (sum : Z) : Prop :=
  (* lst is non-empty *)
  lst <> [] /\
  sum = fold_left
          (fun acc '(i, x) => if (Z.odd i = false) && (Z.even x) then acc + x else acc)
          (combine (seq 0 (Z.of_nat (length lst))) lst) 0 /\
  (* sum of even elements at odd indices *)
  sum = fold_left
          (fun acc '(i, x) =>
            if (Z.eqb (Z.rem i 2) 1) && (Z.eqb (Z.rem x 2) 0) then acc + x else acc)
          (combine (seq 0 (Z.of_nat (length lst))) lst) 0.
