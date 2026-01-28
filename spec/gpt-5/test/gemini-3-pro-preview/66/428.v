Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.

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

Example test_digitSum_long: digitSum_spec "ABCDEThisTHISISALONGSTRINGWITHMANYUPPERCASELETTisEThisTh!s!s$0nly4t3sHELLOthereWHATareYOUdoingTODAY?IHoABCDEFGHIJKLMNOPQRSTUVWXYZTODAY?IHopDeYOURdayISgoingWELL.dm5g55gn5t5Th05t5yn5thy5ht5t5S5t5b5t5m5t5nm5t4K5t5ms5tHisRIsahCrazyMiXofUPPERandloWercaseLENTERS5t5m5t5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t5nRSANDNOSPACES" 11804.
Proof.
  unfold digitSum_spec.
  compute.
  reflexivity.
Qed.