Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

(* Helper function to convert a 1-character string to ascii safely *)
Definition to_ascii (s : string) : ascii :=
  match String.get 0 s with
  | Some c => c
  | None => Ascii.zero
  end.

(* 
   Redefining char_relation using a map to avoid syntax errors with ascii patterns.
   This preserves the logic: lowercase letters are shifted, others are unchanged.
*)
Definition encryption_map : list (ascii * ascii) := [
  (to_ascii "a", to_ascii "e"); (to_ascii "b", to_ascii "f"); (to_ascii "c", to_ascii "g"); (to_ascii "d", to_ascii "h");
  (to_ascii "e", to_ascii "i"); (to_ascii "f", to_ascii "j"); (to_ascii "g", to_ascii "k"); (to_ascii "h", to_ascii "l");
  (to_ascii "i", to_ascii "m"); (to_ascii "j", to_ascii "n"); (to_ascii "k", to_ascii "o"); (to_ascii "l", to_ascii "p");
  (to_ascii "m", to_ascii "q"); (to_ascii "n", to_ascii "r"); (to_ascii "o", to_ascii "s"); (to_ascii "p", to_ascii "t");
  (to_ascii "q", to_ascii "u"); (to_ascii "r", to_ascii "v"); (to_ascii "s", to_ascii "w"); (to_ascii "t", to_ascii "x");
  (to_ascii "u", to_ascii "y"); (to_ascii "v", to_ascii "z"); (to_ascii "w", to_ascii "a"); (to_ascii "x", to_ascii "b");
  (to_ascii "y", to_ascii "c"); (to_ascii "z", to_ascii "d")
].

Definition char_relation (c_in c_out : ascii) : Prop :=
  match find (fun p => Ascii.eqb (fst p) c_in) encryption_map with
  | Some (_, mapped) => c_out = mapped
  | None => c_out = c_in
  end.

Definition problem_89_spec (s : string) (output : string) : Prop :=
  String.length s = String.length output /\
  forall i, i < String.length s ->
    match String.get i s, String.get i output with
    | Some c_in, Some c_out => char_relation c_in c_out
    | _, _ => False
    end.

Example test_problem_89 : problem_89_spec "hi" "lm".
Proof.
  unfold problem_89_spec.
  split.
  - (* Part 1: Prove lengths are equal *)
    simpl. reflexivity.
  - (* Part 2: Prove character relations for each index *)
    intros i H.
    destruct i.
    + (* Case i = 0 *)
      simpl.
      (* Verify 'h' maps to 'l' *)
      vm_compute. reflexivity.
    + destruct i.
      * (* Case i = 1 *)
        simpl.
        (* Verify 'i' maps to 'm' *)
        vm_compute. reflexivity.
      * (* Case i >= 2, which contradicts H (i < 2) *)
        simpl in H.
        repeat apply Nat.lt_S_n in H.
        inversion H.
Qed.