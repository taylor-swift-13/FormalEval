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

Example problem_141_test_example_txt :
  problem_141_spec "example.txt"%string "Yes"%string.
Proof.
  unfold problem_141_spec.
  simpl.
  left. split.
  - split.
    + vm_compute. lia.
    + exists (("e"::"x"::"a"::"m"::"p"::"l"::"e"::[])%char).
      exists (("t"::"x"::"t"::[])%char).
      split.
      * vm_compute. reflexivity.
      * split.
        { intro HIn.
          apply in_app_iff in HIn.
          destruct HIn as [Hin1|Hin2].
          - assert (~ In "."%char (("e"::"x"::"a"::"m"::"p"::"l"::"e"::[])%char)) as Hpref.
            { unfold not. intros H.
              simpl in H.
              destruct H as [He|H]; [vm_compute in He; discriminate|].
              simpl in H.
              destruct H as [Hx|H]; [vm_compute in Hx; discriminate|].
              simpl in H.
              destruct H as [Ha|H]; [vm_compute in Ha; discriminate|].
              simpl in H.
              destruct H as [Hm|H]; [vm_compute in Hm; discriminate|].
              simpl in H.
              destruct H as [Hp|H]; [vm_compute in Hp; discriminate|].
              simpl in H.
              destruct H as [Hl|H]; [vm_compute in Hl; discriminate|].
              simpl in H.
              destruct H as [He2|H]; [vm_compute in He2; discriminate|].
              contradiction.
            }
            apply Hpref in Hin1. contradiction.
          - assert (~ In "."%char (("t"::"x"::"t"::[])%char)) as Hsuf.
            { unfold not. intros H.
              simpl in H.
              destruct H as [Ht|H]; [vm_compute in Ht; discriminate|].
              simpl in H.
              destruct H as [Hx|H]; [vm_compute in Hx; discriminate|].
              simpl in H.
              destruct H as [Ht2|H]; [vm_compute in Ht2; discriminate|].
              contradiction.
            }
            apply Hsuf in Hin2. contradiction.
        }
        split.
        { exists ("e"%char).
          exists (("x"::"a"::"m"::"p"::"l"::"e"::[])%char).
          split; [reflexivity|].
          unfold is_alpha. left.
          vm_compute. split; lia.
        }
        { left. reflexivity. }
  - reflexivity.
Qed.