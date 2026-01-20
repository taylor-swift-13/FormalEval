Require Import Coq.Strings.Ascii Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.Strings.String.
Import ListNotations.

Definition is_uppercase (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (Nat.leb 65 n) && (Nat.leb n 90).

Fixpoint sum_uppercase_ascii (l : list ascii) : nat :=
  match l with
  | [] => 0
  | c :: t =>
    if is_uppercase c
    then nat_of_ascii c + sum_uppercase_ascii t
    else sum_uppercase_ascii t
  end.

Definition digitSum_spec (l : list ascii) (n : nat) : Prop :=
  n = sum_uppercase_ascii l.

Example digitSum_test_long :
  digitSum_spec (list_ascii_of_string "Th!s!s$0nly4t3st!ng-1&2%3*4@5_c@5ES.4305t5n5t5v5ff5mm5g55gn5t5Th5t5yn5thy5ht5t5S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5n5t5r5t5s5t5n5n5M5tTHTHISISALONGSTRINGWITHMANYUPPERCASEL12345ABCDEFGHJIJKLMNOPQRSTUVWXYZ67890ETTHERSANDNTh!s!s$0nly4t3st!ng-1&2%3*4@5_c@5ES.4305t5n5t5v5ff5mm5g55gn5t5Th5t5yn5thytHisIeLENTERSercaseLENTERS5t5m5t5sn5ST5TS5t5aaaaabbbbbbccccccdddeeefffggggHHHHHIIIIJJJJKKKKLLLLMMMMNNNNOOOOPPPQQQQRRRRSSSSTTTTUUVVVVWWWXXXYYYZZMZn5t5n5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t5nwitWOWTHISISSUCHALONGSTRINTGIWONDERIFIaaaaabbbbbbccccccdddeeefffggggHHHHHIIIIJJJJKKKKLLLLMMMMNNNNOOOOPPPQQQQRRRRSSSSTTTTUUVVVVWWWXXXYYYZZZTWILLOVERFLOWMYTEXTEDITOROREVENALARGBUFFER.ITSJUSTSOMANYUPPERCASELETTERS.OSPACESNDNOSPACES5s5t5m5t5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t5n") 29955.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.