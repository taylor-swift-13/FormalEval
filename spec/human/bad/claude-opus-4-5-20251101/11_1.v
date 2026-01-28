Require Import List.
Require Import Ascii.
Require Import String.
Require Import Bool.
Require Import Arith.
Require Import Lia.
Import ListNotations.
Open Scope string_scope.

(* Pre: inputs have equal length and contain only '0' or '1' characters *)
Definition problem_11_pre (a b : string) : Prop :=
  String.length a = String.length b /\
  forall i,
    i < String.length a ->
      ((String.get i a = Some "0"%char) \/ (String.get i a = Some "1"%char)) /\
      ((String.get i b = Some "0"%char) \/ (String.get i b = Some "1"%char)).

(* 定义 Spec 规约 *)

Definition problem_11_spec (a b output : string) : Prop :=
  String.length a = String.length b /\
  String.length output = String.length a /\
  forall i,
    i < String.length output ->
    (String.get i a = String.get i b -> String.get i output = Some "0"%char) /\
    (String.get i a <> String.get i b -> String.get i output = Some "1"%char).

Example problem_11_test :
  problem_11_spec "111000" "101010" "010010".
Proof.
  unfold problem_11_spec.
  repeat split.
  - (* String.length "111000" = String.length "101010" *)
    reflexivity.
  - (* String.length "010010" = String.length "111000" *)
    reflexivity.
  - (* forall i, ... *)
    intros i Hi.
    simpl in Hi.
    split.
    + (* String.get i a = String.get i b -> String.get i output = Some "0" *)
      intro Heq.
      (* Case analysis on i from 0 to 5 *)
      destruct i as [| [| [| [| [| [| n]]]]]].
      * (* i = 0: a[0]='1', b[0]='1', equal, output[0]='0' *)
        simpl in Heq. simpl. reflexivity.
      * (* i = 1: a[1]='1', b[1]='0', not equal *)
        simpl in Heq. inversion Heq.
      * (* i = 2: a[2]='1', b[2]='1', equal, output[2]='0' *)
        simpl in Heq. simpl. reflexivity.
      * (* i = 3: a[3]='0', b[3]='0', equal, output[3]='0' *)
        simpl in Heq. simpl. reflexivity.
      * (* i = 4: a[4]='0', b[4]='1', not equal *)
        simpl in Heq. inversion Heq.
      * (* i = 5: a[5]='0', b[5]='0', equal, output[5]='0' *)
        simpl in Heq. simpl. reflexivity.
      * (* i >= 6: contradiction *)
        lia.
    + (* String.get i a <> String.get i b -> String.get i output = Some "1" *)
      intro Hneq.
      destruct i as [| [| [| [| [| [| n]]]]]].
      * (* i = 0: a[0]='1', b[0]='1', equal - contradiction *)
        simpl in Hneq. exfalso. apply Hneq. reflexivity.
      * (* i = 1: a[1]='1', b[1]='0', not equal, output[1]='1' *)
        simpl. reflexivity.
      * (* i = 2: a[2]='1', b[2]='1', equal - contradiction *)
        simpl in Hneq. exfalso. apply Hneq. reflexivity.
      * (* i = 3: a[3]='0', b[3]='0', equal - contradiction *)
        simpl in Hneq. exfalso. apply Hneq. reflexivity.
      * (* i = 4: a[4]='0', b[4]='1', not equal, output[4]='1' *)
        simpl. reflexivity.
      * (* i = 5: a[5]='0', b[5]='0', equal - contradiction *)
        simpl in Hneq. exfalso. apply Hneq. reflexivity.
      * (* i >= 6: contradiction *)
        lia.
Qed.