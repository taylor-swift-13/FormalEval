Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Import Coq.omega.Omega.
Import ListNotations.

Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

(* --- Specification Definitions --- *)

Definition char_to_nat (c : ascii) : nat := nat_of_ascii c.

Definition sorted_by_ascii (l : list ascii) : list ascii :=
  let fix insert (c : ascii) (sorted : list ascii) : list ascii :=
    match sorted with
    | [] => [c]
    | h :: t => if Nat.leb (char_to_nat c) (char_to_nat h)
                then c :: sorted
                else h :: insert c t
    end
  in
  fold_right insert [] l.

Definition is_sorted_by_ascii (l : list ascii) : Prop :=
  forall i j, i < j -> j < length l ->
    char_to_nat (nth i l zero) <= char_to_nat (nth j l zero).

Definition is_permutation (l1 l2 : list ascii) : Prop :=
  forall c : ascii, count_occ ascii_dec l1 c = count_occ ascii_dec l2 c.

Definition string_to_list (s : string) : list ascii :=
  list_ascii_of_string s.

Definition list_to_string (l : list ascii) : string :=
  string_of_list_ascii l.

Fixpoint split_by_space (s : string) : list string :=
  match s with
  | EmptyString => [EmptyString]
  | String c rest =>
    if (nat_of_ascii c =? 32)%nat then
      EmptyString :: split_by_space rest
    else
      match split_by_space rest with
      | [] => [String c EmptyString]
      | h :: t => (String c h) :: t
      end
  end.

Fixpoint join_with_space (words : list string) : string :=
  match words with
  | [] => EmptyString
  | [w] => w
  | w :: rest => append w (String " "%char (join_with_space rest))
  end.

Definition sort_word (w : string) : string :=
  list_to_string (sorted_by_ascii (string_to_list w)).

Definition anti_shuffle_spec (s : string) (result : string) : Prop :=
  let input_words := split_by_space s in
  let output_words := split_by_space result in
  length input_words = length output_words /\
  (forall i, i < length input_words ->
    let in_word := nth i input_words EmptyString in
    let out_word := nth i output_words EmptyString in
    is_permutation (string_to_list in_word) (string_to_list out_word) /\
    is_sorted_by_ascii (string_to_list out_word)) /\
  result = join_with_space (map sort_word input_words).

(* --- Test Case Proof --- *)

Example test_anti_shuffle_hi : anti_shuffle_spec "Hi" "Hi".
Proof.
  unfold anti_shuffle_spec.
  
  (* Simplify the let-bindings and list structures *)
  simpl.
  
  (* Split the conjunctions *)
  repeat split.
  
  (* 1. Length equality: 1 = 1 *)
  - reflexivity.
  
  (* 2. Properties for the single word at index 0 *)
  - intros i Hi.
    destruct i.
    + (* Case i = 0 *)
      simpl.
      split.
      * (* is_permutation: "Hi" is a permutation of "Hi" *)
        unfold is_permutation.
        intro c.
        reflexivity.
      * (* is_sorted_by_ascii: "Hi" is sorted *)
        unfold is_sorted_by_ascii.
        intros j k Hjk Hlen.
        (* Analyze indices j and k for list of length 2 *)
        destruct j.
        -- (* j = 0 *)
           destruct k.
           ++ (* k = 0, contradiction with j < k *)
              omega.
           ++ (* k = 1 *)
              destruct k.
              ** (* k = 1. Compare 'H' (72) and 'i' (105) *)
                 simpl.
                 (* Reduce ascii to nat to prove 72 <= 105 *)
                 cbv.
                 omega.
              ** (* k > 1, out of bounds *)
                 simpl in Hlen. omega.
        -- (* j > 0 *)
           destruct j.
           ++ (* j = 1, implies k >= 2, out of bounds *)
              simpl in Hlen. omega.
           ++ (* j > 1, out of bounds *)
              simpl in Hlen. omega.
    + (* Case i > 0, contradiction with length 1 *)
      simpl in Hi. omega.
      
  (* 3. Result construction check *)
  - (* Verify that "Hi" equals the sorted version of "Hi" joined *)
    (* We use vm_compute to evaluate the sorting and string operations *)
    vm_compute.
    reflexivity.
Qed.