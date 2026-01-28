Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Lia.

Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.

(* --- Specification Definitions --- *)

Fixpoint value_base_acc (base : Z) (acc : Z) (ds : list Z) : Z :=
  match ds with
  | nil => acc
  | d :: rest => value_base_acc base (base * acc + d) rest
  end.

Definition value_base_Z (base : Z) (ds : list Z) : Z :=
  value_base_acc base 0 ds.

Fixpoint sum_list_Z (ds : list Z) : Z :=
  match ds with
  | nil => 0
  | d :: rest => d + sum_list_Z rest
  end.

Definition decimal_digits_of (N : Z) (ds : list Z) : Prop :=
  (forall d, In d ds -> 0 <= d <= 9) /\
  value_base_Z 10 ds = N /\
  ((N = 0 /\ ds = (0 :: nil)) \/
   (N <> 0 /\ exists d rest, ds = d :: rest /\ d <> 0)).

Definition bit_to_Z (b : bool) : Z := if b then 1 else 0.

Fixpoint string_of_bits (bs : list bool) : string :=
  match bs with
  | nil => EmptyString
  | b :: rest => String (if b then "1"%char else "0"%char) (string_of_bits rest)
  end.

Definition value_bits (bits : list bool) : Z :=
  value_base_acc 2 0 (map bit_to_Z bits).

Definition binary_string_of (s : Z) (out : string) : Prop :=
  exists bits,
    value_bits bits = s /\
    ((s = 0 /\ bits = (false :: nil)) \/
     (s <> 0 /\ exists rest, bits = true :: rest)) /\
    out = string_of_bits bits.

Definition solve_spec (N : Z) (out : string) : Prop :=
  0 <= N <= 10000 /\
  exists ds s,
    decimal_digits_of N ds /\
    s = sum_list_Z ds /\
    binary_string_of s out.

(* --- Proof --- *)

Example test_case : solve_spec 4443 "1111".
Proof.
  (* Unfold the main specification *)
  unfold solve_spec.
  split.
  - (* Prove bounds: 0 <= 4443 <= 10000 *)
    lia.
  - (* Provide witnesses for ds (digits of 4443) and s (sum of digits) *)
    exists [4; 4; 4; 3]%Z.
    exists 15%Z.
    split.
    + (* Prove decimal_digits_of 4443 [4; 4; 4; 3] *)
      unfold decimal_digits_of.
      split.
      * (* Prove all digits are between 0 and 9 *)
        intros d H.
        simpl in H.
        (* Break down the list inclusion *)
        repeat destruct H as [H | H]; subst; lia.
      * split.
        -- (* Prove value_base_Z 10 [4; 4; 4; 3] = 4443 *)
           simpl. reflexivity.
        -- (* Prove canonical representation *)
           right.
           split.
           ++ lia. (* 4443 <> 0 *)
           ++ exists 4%Z, [4; 4; 3]%Z.
              split; [reflexivity | lia].
    + split.
      * (* Prove s = sum_list_Z [4; 4; 4; 3] *)
        simpl. reflexivity.
      * (* Prove binary_string_of 15 "1111" *)
        unfold binary_string_of.
        (* Provide witness for bits *)
        exists [true; true; true; true].
        split.
        -- (* Prove value_bits [true; true; true; true] = 15 *)
           unfold value_bits.
           simpl. reflexivity.
        -- split.
           ++ (* Prove canonical bit representation for non-zero *)
              right.
              split.
              ** lia. (* 15 <> 0 *)
              ** exists [true; true; true]. reflexivity.
           ++ (* Prove string generation *)
              simpl. reflexivity.
Qed.