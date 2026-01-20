Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Import ListNotations.

Section PalindromeSpec.
  Variable A : Type.

  Definition is_palindrome (l : list A) : Prop :=
    l = rev l.

  Definition make_palindrome_spec (s : list A) (res : list A) : Prop :=
    exists (p q : list A),
      s = p ++ q /\
      is_palindrome q /\
      res = s ++ rev p /\
      (forall (p' q' : list A),
         s = p' ++ q' -> is_palindrome q' -> length p <= length p').

End PalindromeSpec.

(* 
   Test case: input = [""], output = ""
   Interpreted as: input list s is empty [], output list res is empty [].
   This holds for any type A.
*)
Example test_palindrome_empty {A : Type} : make_palindrome_spec A [] [].
Proof.
  unfold make_palindrome_spec.
  (* We choose p = [] and q = [] which satisfies the specification *)
  exists [], [].
  repeat split.
  - (* Check s = p ++ q: [] = [] ++ [] *)
    simpl. reflexivity.
  - (* Check is_palindrome q: [] = rev [] *)
    unfold is_palindrome. simpl. reflexivity.
  - (* Check res = s ++ rev p: [] = [] ++ rev [] *)
    simpl. reflexivity.
  - (* Check minimality: forall p' q', s = p' ++ q' -> is_palindrome q' -> length p <= length p' *)
    intros p' q' H_eq H_pal.
    simpl.
    (* Goal is 0 <= length p', which is true for any natural number *)
    apply le_0_n.
Qed.