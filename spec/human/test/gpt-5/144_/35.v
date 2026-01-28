Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Import ListNotations.

Definition char_to_digit (c : ascii) : nat :=
  let n := nat_of_ascii c in
  let zero := nat_of_ascii ("0"%char) in
  n - zero.

Inductive list_ascii_to_nat_rel : list ascii -> nat -> Prop :=
| latn_nil : list_ascii_to_nat_rel [] 0
| latn_cons : forall c l n,
    list_ascii_to_nat_rel l n ->
    list_ascii_to_nat_rel (l ++ [c]) (n * 10 + char_to_digit c).

Definition Parse_Fraction (s : list ascii) (num den : nat) : Prop :=
  exists num_s den_s : list ascii,
    s = num_s ++ ["/"%char] ++ den_s /\
    list_ascii_to_nat_rel num_s num /\
    list_ascii_to_nat_rel den_s den.

Definition problem_144_pre (x n : string) : Prop :=
  exists nx dx ny dy,
    Parse_Fraction (list_ascii_of_string x) nx dx /\
    Parse_Fraction (list_ascii_of_string n) ny dy /\
    nx > 0 /\ dx > 0 /\ ny > 0 /\ dy > 0.

Definition problem_144_spec (x n : string) (output : bool) : Prop :=
  exists num_x den_x num_n den_n : nat,
    Parse_Fraction (list_ascii_of_string x) num_x den_x /\
    Parse_Fraction (list_ascii_of_string n) num_n den_n /\
    num_x > 0 /\ den_x > 0 /\
    num_n > 0 /\ den_n > 0 /\
    let product_num := num_x * num_n in
    let product_den := den_x * den_n in
    output = if (product_num mod product_den) =? 0
             then true
             else false.

Example test_simplify_1 : problem_144_spec "133/19"%string "13/19"%string false.
Proof.
  unfold problem_144_spec.
  exists 133, 19, 13, 19.
  split.
  - unfold Parse_Fraction.
    exists (list_ascii_of_string "133"%string), (list_ascii_of_string "19"%string).
    split.
    + simpl. reflexivity.
    + split.
      * simpl.
        apply (latn_cons "3"%char ["1"%char; "3"%char] 13).
        apply (latn_cons "3"%char ["1"%char] 1).
        apply (latn_cons "1"%char [] 0).
        apply latn_nil.
      * simpl.
        apply (latn_cons "9"%char ["1"%char] 1).
        apply (latn_cons "1"%char [] 0).
        apply latn_nil.
  - split.
    + unfold Parse_Fraction.
      exists (list_ascii_of_string "13"%string), (list_ascii_of_string "19"%string).
      split.
      * simpl. reflexivity.
      * split.
        -- simpl.
           apply (latn_cons "3"%char ["1"%char] 1).
           apply (latn_cons "1"%char [] 0).
           apply latn_nil.
        -- simpl.
           apply (latn_cons "9"%char ["1"%char] 1).
           apply (latn_cons "1"%char [] 0).
           apply latn_nil.
    + split.
      * vm_compute; lia.
      * split.
        -- vm_compute; lia.
        -- split.
           ++ vm_compute; lia.
           ++ split.
              ** vm_compute; lia.
              ** simpl.
                 vm_compute.
                 reflexivity.
Qed.