Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Arith.
Require Import Lia.
Import ListNotations.
Open Scope string_scope.

Definition problem_80_pre (s : string) : Prop := True.

Definition problem_80_spec (s : string) (output : bool) : Prop :=
  let len := String.length s in
  match output with
  | true => 
    (len >= 3)%nat /\
    (forall i : nat, (i + 2 < len)%nat ->
      let default_char := Ascii.ascii_of_nat 0 in 
      let c1 := String.get i s in
      let c2 := String.get (i + 1) s in
      let c3 := String.get (i + 2) s in
      c1 <> c2 /\ c1 <> c3 /\ c2 <> c3)
  | false => 
    (len < 3)%nat \/
    (exists i : nat, (i + 2 < len)%nat /\
      (let default_char := Ascii.ascii_of_nat 0 in
       let c1 := String.get i s in
       let c2 := String.get (i + 1) s in
       let c3 := String.get (i + 2) s in
       c1 = c2 \/ c1 = c3 \/ c2 = c3))
  end.

Example test_is_happy_fail_short: problem_80_spec "a" false.
Proof.
  (* Unfold the definition of the specification *)
  unfold problem_80_spec.
  
  (* Simplify the expression. 
     String.length "a" computes to 1.
     The match expression reduces to the false branch. *)
  simpl.
  
  (* The goal is now a disjunction: (1 < 3)%nat \/ ... 
     Since the length is indeed less than 3, we prove the left side. *)
  left.
  
  (* Prove that 1 < 3 using linear integer arithmetic *)
  lia.
Qed.