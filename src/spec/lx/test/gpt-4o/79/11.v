Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Open Scope string_scope.

Inductive IsBinaryRepr : nat -> list bool -> Prop :=
  | BZ: IsBinaryRepr 0 [false]
  | B1: IsBinaryRepr 1 [true]
  | BEven (n : nat) (l : list bool) :
      n > 0 -> IsBinaryRepr n l -> IsBinaryRepr (2 * n) (l ++ [false])
  | BOdd (n : nat) (l : list bool) :
      n > 0 -> IsBinaryRepr n l -> IsBinaryRepr (2 * n + 1) (l ++ [true]).

Fixpoint binary_list_to_string (l : list bool) : string :=
  match l with
  | [] => ""
  | b :: tl => (if b then "1" else "0") ++ binary_list_to_string tl
  end.

Definition decimal_to_binary_spec (decimal : nat) (output : string) : Prop :=
  exists (bl : list bool),
    IsBinaryRepr decimal bl /\
    output = "db" ++ binary_list_to_string bl ++ "db".

Example decimal_to_binary_test_1 :
  decimal_to_binary_spec 1 "db1db".
Proof.
  unfold decimal_to_binary_spec.
  exists [true].
  split.
  - apply B1.
  - simpl. reflexivity.
Qed.