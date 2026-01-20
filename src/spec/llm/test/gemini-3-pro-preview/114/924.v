Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Import ListNotations.
Open Scope Z_scope.

Definition is_even (n : Z) : bool := Z.even n.

Definition is_odd (n : Z) : bool := negb (Z.even n).

Definition solve (l : list Z) : Z :=
  let odds := filter is_odd l in
  let neg_evens := filter (fun x => is_even x && (x <? 0)) l in
  let min_odd := match odds with
                 | [] => 0
                 | x :: xs => fold_right Z.min x xs
                 end in
  let min_neg_even := match neg_evens with
                      | [] => 0
                      | x :: xs => fold_right Z.min x xs
                      end in
  min_odd + min_neg_even.

Example test_case_new : solve [50; -50; 100; -100; -99; 50; 100; -100; 50; -50; 100; -100; 50; -50; 100; 50; -50; 100; -100] = -199.
Proof. reflexivity. Qed.