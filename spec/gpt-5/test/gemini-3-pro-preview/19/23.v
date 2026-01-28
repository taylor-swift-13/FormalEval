Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.

Local Open Scope string_scope.

Fixpoint join_with_space (l : list string) : string :=
  match l with
  | nil => ""
  | cons h nil => h
  | cons h t => h ++ " " ++ join_with_space t
  end.

Definition valid_word (s : string) : Prop :=
  s = "zero" \/
  s = "one" \/
  s = "two" \/
  s = "three" \/
  s = "four" \/
  s = "five" \/
  s = "six" \/
  s = "seven" \/
  s = "eight" \/
  s = "nine".

Definition val_of (s : string) : nat :=
  match s with
  | "zero" => 0
  | "one" => 1
  | "two" => 2
  | "three" => 3
  | "four" => 4
  | "five" => 5
  | "six" => 6
  | "seven" => 7
  | "eight" => 8
  | "nine" => 9
  | _ => 0
  end.

Definition sort_numbers_spec (numbers : string) (result : string) : Prop :=
  (numbers = "" /\ result = "") \/
  exists l l',
    join_with_space l = numbers /\
    Forall valid_word l /\
    Permutation l l' /\
    Sorted (fun s1 s2 => val_of s1 <= val_of s2) l' /\
    result = join_with_space l'.

Example test_sort_numbers : sort_numbers_spec "zero five seven" "zero five seven".
Proof.
  unfold sort_numbers_spec.
  right.
  exists ("zero" :: "five" :: "seven" :: nil).
  exists ("zero" :: "five" :: "seven" :: nil).
  split.
  - (* join_with_space *)
    simpl. reflexivity.
  - split.
    + (* Forall valid_word *)
      constructor.
      * left. reflexivity.
      * constructor.
        -- right. right. right. right. right. left. reflexivity.
        -- constructor.
           ++ right. right. right. right. right. right. right. left. reflexivity.
           ++ constructor.
    + split.
      * (* Permutation *)
        apply Permutation_refl.
      * split.
        -- (* Sorted *)
           apply Sorted_cons.
           ++ apply Sorted_cons.
              ** apply Sorted_cons.
                 --- apply Sorted_nil.
                 --- apply HdRel_nil.
              ** apply HdRel_cons. simpl. repeat constructor.
           ++ apply HdRel_cons. simpl. repeat constructor.
        -- (* result *)
           simpl. reflexivity.
Qed.