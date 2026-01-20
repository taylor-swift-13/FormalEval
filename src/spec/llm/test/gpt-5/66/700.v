Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.ZArith.ZArith.

Open Scope string_scope.

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

Definition s_big :=
  "tabsBCDEtHisIsaCrazyMiXofRUPPERandloWercaseLENTERSFTGHIJKLMNOPQRSTUVThis"
  ++ String (ascii_of_nat 10)
     ("is" ++ String (ascii_of_nat 9) "tabsBCDEFGHIJKLMNOPQRS")
  ++ String (ascii_of_nat 10)
     ("is" ++ String (ascii_of_nat 9) "a"
           ++ String (ascii_of_nat 9) "test"
           ++ String (ascii_of_nat 9) "with")
  ++ String (ascii_of_nat 10)
     ("newlines" ++ String (ascii_of_nat 9) "and"
                 ++ String (ascii_of_nat 9) "tabsWXYAThisZa"
                 ++ String (ascii_of_nat 9) "test"
                 ++ String (ascii_of_nat 9) "tabsWDXYZ").

Example digitSum_big_spec: digitSum_spec s_big 5513.
Proof.
  unfold digitSum_spec.
  simpl.
  reflexivity.
Qed.

Example digitSum_big_Z: Z.of_nat (digitSum_fun s_big) = 5513%Z.
Proof.
  simpl.
  reflexivity.
Qed.