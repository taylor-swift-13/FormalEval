Require Import Coq.Strings.Ascii Coq.Lists.List Coq.Strings.String.
Require Import Coq.Arith.Arith.
Import ListNotations.
Open Scope string_scope.

Definition is_uppercase (c : ascii) : bool :=
  let n := nat_of_ascii c in (Nat.leb 65 n) && (Nat.leb n 90).

Fixpoint sum_uppercase_ascii (s : string) : nat :=
  match s with
  | "" => 0
  | String c s' => if is_uppercase c then nat_of_ascii c + sum_uppercase_ascii s'
              else sum_uppercase_ascii s'
  end.

Definition digitSum_impl (s : string) : nat := sum_uppercase_ascii s.

Definition problem_66_pre (s : string) : Prop := True.

Definition problem_66_spec (s : string) (output : nat) : Prop :=
  output = digitSum_impl s.

Example Example_test : problem_66_spec "This
istHisOVERFLOWMYTEXTEDITORORETh!s!s$0nly4t3st!ng-1&2%3*4@5_c@5ES.4305t5n5t5v5ff5mm5g55gn5t5Th5t5yn5thy5ht5t55S5t5b5t5m5t5nms5t4K5t5ms512345ABCDEFGHJIJKLMNOPQRSTUIVW12345ABCDEFGHJIJKLMNOPQRSTUVWXYWOWTHISISSUCHALONGSTRINGIWONDERIFITWILLOVERFLOWMYTEXTEDITOROREVENALARGBUFFER.ITSOMANYUPPERCASELETTERS.Z67890XYWOWTHISISSUCHALONGSTRINGIWONDERIFITWILLOVERFUPPERCASELETTERS.Z697890tHisRIsaCrazyMiXofUPPERandloWercaseLENTE5RS5t5m5t5sn5ST5TS5t5n5t5n5t5Ar5t5pn5t5shr5t5SS5t5v5t5sn5t5M5t5nVENALARGBUFFER.ITSJUSTSOMANYUPPERCATERS.WercaseLENTNERS	a	test	with
newlines	ans" 24775.
Proof.
  unfold problem_66_spec.
  unfold digitSum_impl.
  vm_compute.
  reflexivity.
Qed.