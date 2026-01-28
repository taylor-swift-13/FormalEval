Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Bool.Bool.
Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Definition has_duplicates (l : list Z) : Z :=
  if (fix aux (l : list Z) : bool :=
        match l with
        | [] => false
        | x :: xs => existsb (Z.eqb x) xs || aux xs
        end) l
  then 1
  else 0.

Example test_case : has_duplicates [39; 104; 152; 240; 152] = 1.
Proof.
  reflexivity.
Qed.