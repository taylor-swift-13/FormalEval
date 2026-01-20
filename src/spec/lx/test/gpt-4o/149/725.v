Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Permutation.
Import ListNotations.

Fixpoint lex_le (s1 s2 : list ascii) : Prop :=
  match s1, s2 with
  | [], _ => True
  | _::_, [] => False
  | c1::s1', c2::s2' =>
    match Ascii.compare c1 c2 with
    | Lt => True
    | Gt => False
    | Eq => lex_le s1' s2'
    end
  end.

Definition string_le (s1 s2 : list ascii) : Prop :=
  match Nat.compare (length s1) (length s2) with
  | Lt => True
  | Gt => False
  | Eq => lex_le s1 s2
  end.

Inductive Sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
| sorted_nil : Sorted R []
| sorted_one : forall x, Sorted R [x]
| sorted_cons : forall x y l, R x y -> Sorted R (y :: l) -> Sorted R (x :: y :: l).

Definition has_even_length (s : list ascii) : bool :=
  Nat.even (length s).

Definition Spec (lst_in lst_out : list (list ascii)) : Prop :=
  Permutation lst_out (filter has_even_length lst_in) /\
  Sorted string_le lst_out.

Example sorted_list_sum_test :
  Spec [["a"%char; "b"%char; "c"%char]; ["i"%char; "s"%char; "i"%char]; ["j"%char; "k"%char; "l"%char];
        ["m"%char; "n"%char; "o"%char]; ["j"%char; "k"%char; "l"%char]; ["a"%char; "b"%char; "c"%char];
        ["m"%char; "n"%char; "o"%char]]
       [].
Proof.
  unfold Spec.
  split.
  - simpl. reflexivity.
  - apply sorted_nil.
Qed.