Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.Arith.PeanoNat.
Require Import Lia.
Import ListNotations.
Import Nat.

Definition is_digit_bool (c : ascii) : bool :=
  let n := nat_of_ascii c in
  (nat_of_ascii "0"%char <=? n) && (n <=? nat_of_ascii "9"%char).

Definition is_alpha (c : ascii) : Prop :=
  let n := nat_of_ascii c in
  (nat_of_ascii "a"%char <= n /\ n <= nat_of_ascii "z"%char) \/
  (nat_of_ascii "A"%char <= n /\ n <= nat_of_ascii "Z"%char).

Definition problem_141_pre (file_name : string) : Prop := True.

Definition problem_141_spec (file_name_str : string) (result : string) : Prop :=
  let file_name := list_ascii_of_string file_name_str in
  let is_valid :=
    (length (filter is_digit_bool file_name) <= 3) /\
    (exists prefix suffix,
      file_name = prefix ++ "."%char :: suffix /\
      ~ In "."%char (prefix ++ suffix) /\
      (exists first_char rest_prefix,
        prefix = first_char :: rest_prefix /\ is_alpha first_char) /\
      (suffix = ("t"::"x"::"t"::[])%char \/
       suffix = ("e"::"x"::"e"::[])%char \/
       suffix = ("d"::"l"::"l"::[])%char))
  in
  (is_valid /\ result = "Yes"%string) \/
  (~is_valid /\ result = "No"%string).

Example problem_141_test_MY16FILE3_exe :
  problem_141_spec "MY16FILE3.exe"%string "Yes"%string.
Proof.
  unfold problem_141_spec.
  simpl.
  left. split.
  - split.
    + vm_compute. lia.
    + exists (("M"::"Y"::"1"::"6"::"F"::"I"::"L"::"E"::"3"::[])%char).
      exists (("e"::"x"::"e"::[])%char).
      split.
      * vm_compute. reflexivity.
      * split.
        { intro HIn.
          apply in_app_iff in HIn.
          destruct HIn as [Hin1|Hin2].
          - assert (~ In "."%char (("M"::"Y"::"1"::"6"::"F"::"I"::"L"::"E"::"3"::[])%char)) as Hpref.
            { unfold not. intros H.
              simpl in H.
              destruct H as [HM|H]; [vm_compute in HM; discriminate|].
              simpl in H.
              destruct H as [HY|H]; [vm_compute in HY; discriminate|].
              simpl in H.
              destruct H as [H1|H]; [vm_compute in H1; discriminate|].
              simpl in H.
              destruct H as [H6|H]; [vm_compute in H6; discriminate|].
              simpl in H.
              destruct H as [HF|H]; [vm_compute in HF; discriminate|].
              simpl in H.
              destruct H as [HI|H]; [vm_compute in HI; discriminate|].
              simpl in H.
              destruct H as [HL|H]; [vm_compute in HL; discriminate|].
              simpl in H.
              destruct H as [HE|H]; [vm_compute in HE; discriminate|].
              simpl in H.
              destruct H as [H3|H]; [vm_compute in H3; discriminate|].
              contradiction.
            }
            apply Hpref in Hin1. contradiction.
          - assert (~ In "."%char (("e"::"x"::"e"::[])%char)) as Hsuf.
            { unfold not. intros H.
              simpl in H.
              destruct H as [He|H]; [vm_compute in He; discriminate|].
              simpl in H.
              destruct H as [Hx|H]; [vm_compute in Hx; discriminate|].
              simpl in H.
              destruct H as [He2|H]; [vm_compute in He2; discriminate|].
              contradiction.
            }
            apply Hsuf in Hin2. contradiction.
        }
        split.
        { exists ("M"%char).
          exists (("Y"::"1"::"6"::"F"::"I"::"L"::"E"::"3"::[])%char).
          split; [reflexivity|].
          unfold is_alpha. right.
          vm_compute. split; lia.
        }
        { right. left. reflexivity. }
  - reflexivity.
Qed.