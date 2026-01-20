From Coq Require Import ZArith.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.

Import ListNotations.

Local Open Scope Z_scope.
Local Open Scope string_scope.

Fixpoint sumZ (l : list Z) : Z :=
  match l with
  | [] => 0%Z
  | x :: xs => x + sumZ xs
  end.

Definition spec (l : list Z) : string :=
  if Z.eqb (2%Z * sumZ l) 22%Z then "22" else "".

Example test_case :
  spec [8%Z; 3%Z] = "22".
Proof.
  unfold spec.
  simpl.
  reflexivity.
Qed.