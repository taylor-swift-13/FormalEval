Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Fixpoint digitSum_fun (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String ch rest =>
      let code := nat_of_ascii ch in
      let is_upper := andb (Nat.leb 65 code) (Nat.leb code 90) in
      (if is_upper then code else 0) + digitSum_fun rest
  end.

Definition digitSum_spec (s : string) (sum : nat) : Prop :=
  sum = digitSum_fun s.

Example digitSum_long_spec: digitSum_spec "WOWTHISISSUCHALONGSTRINGIWONDERIFITWILLOVERFLOWMYTEXTEDITOROREVENALARGBUFFER.ITSJUSTSOMANYUPPERCAtetHTh!s!s$0nly4t3st!ng-f5mm5g55gn5t5Th5t5yn5thy5ht5t5S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5nt5t5r5t12345ABCSTUVWXYZ67890estt5s5tt5v5t5sn5t5M5t1A$Bc&Def3@F5nisIsaCrazyMiXofUPPERaTh!s!s$0nly4t3sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SSaaaaabbbbbbccccccdddeeefffggggHHHHHIIIHELLOthereWHATareYOUdoingTODAY?IHopeYOURdayISgoingWELL.IJJJJGHIJKLMNOPQRSTUVThisVVVVWWWXXXYYYZZZ5t5v5t5sn5t5M5t5nLENTERStSELETTERS." 17676.
Proof.
  unfold digitSum_spec.
  vm_compute.
  reflexivity.
Qed.

Example digitSum_long_Z: Z.of_nat (digitSum_fun "WOWTHISISSUCHALONGSTRINGIWONDERIFITWILLOVERFLOWMYTEXTEDITOROREVENALARGBUFFER.ITSJUSTSOMANYUPPERCAtetHTh!s!s$0nly4t3st!ng-f5mm5g55gn5t5Th5t5yn5thy5ht5t5S5t5b5t5m5t5nm5t4K5t5ms5t5m5t5nt5t5r5t12345ABCSTUVWXYZ67890estt5s5tt5v5t5sn5t5M5t1A$Bc&Def3@F5nisIsaCrazyMiXofUPPERaTh!s!s$0nly4t3sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SSaaaaabbbbbbccccccdddeeefffggggHHHHHIIIHELLOthereWHATareYOUdoingTODAY?IHopeYOURdayISgoingWELL.IJJJJGHIJKLMNOPQRSTUVThisVVVVWWWXXXYYYZZZ5t5v5t5sn5t5M5t5nLENTERStSELETTERS.") = 17676%Z.
Proof.
  vm_compute.
  reflexivity.
Qed.