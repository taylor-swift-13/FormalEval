(* Required imports *)
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.PeanoNat.
Require Import Permutation.
Import ListNotations.

(* Definition of lex_le *)
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

(* Definition of string_le *)
Definition string_le (s1 s2 : list ascii) : Prop :=
  match Nat.compare (length s1) (length s2) with
  | Lt => True
  | Gt => False
  | Eq => lex_le s1 s2
  end.

(* Definition of Sorted *)
Inductive Sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop :=
| sorted_nil : Sorted R []
| sorted_one : forall x, Sorted R [x]
| sorted_cons : forall x y l, R x y -> Sorted R (y :: l) -> Sorted R (x :: y :: l).

(* Definition of has_even_length *)
Definition has_even_length (s : list ascii) : bool :=
  Nat.even (length s).

(* Specification *)
Definition Spec (lst_in lst_out : list (list ascii)) : Prop :=
  Permutation lst_out (filter has_even_length lst_in) /\
  Sorted string_le lst_out.

(* Test case *)
Example sorted_list_sum_test :
  Spec [["p"%char; "r"%char; "l"%char; "d"%char; "y"%char; "y"%char; "a"%char; "b"%char; "c"%char; "d"%char];
        ["j"%char; "i"%char; "s"%char];
        ["m"%char; "n"%char; "e"%char; "e"%char; "o"%char];
        ["e"%char; "f"%char; "g"%char];
        ["h"%char; "i"%char];
        ["j"%char; "k"%char; "w"%char; "o"%char; "r"%char; "l"%char; "l"%char; "d"%char; "l"%char];
        ["j"%char; "k"%char; "l"%char];
        ["m"%char; "n"%char; "o"%char];
        ["j"%char; "k"%char; "l"%char]]
       [["h"%char; "i"%char];
        ["p"%char; "r"%char; "l"%char; "d"%char; "y"%char; "y"%char; "a"%char; "b"%char; "c"%char; "d"%char]].
Proof.
  unfold Spec.
  split.
  - (* Permutation proof *)
    simpl.
    apply perm_swap.
  - (* Sorted proof *)
    apply sorted_cons.
    + unfold string_le. simpl. reflexivity.
    + apply sorted_one.
Qed.