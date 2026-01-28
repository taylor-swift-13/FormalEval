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

Example problem_141_test_this_is_valid_txt :
  problem_141_spec "this_is_valid.txt"%string "Yes"%string.
Proof.
  unfold problem_141_spec.
  simpl.
  left. split.
  - split.
    + vm_compute. lia.
    + exists (("t"::"h"::"i"::"s"::"_"::"i"::"s"::"_"::"v"::"a"::"l"::"i"::"d"::[])%char).
      exists (("t"::"x"::"t"::[])%char).
      split.
      * vm_compute. reflexivity.
      * split.
        { intro HIn.
          apply in_app_iff in HIn.
          destruct HIn as [Hin1|Hin2].
          - assert (~ In "."%char (("t"::"h"::"i"::"s"::"_"::"i"::"s"::"_"::"v"::"a"::"l"::"i"::"d"::[])%char)) as Hpref.
            { unfold not. intros H.
              simpl in H.
              destruct H as [Ht|H]; [vm_compute in Ht; discriminate|].
              simpl in H.
              destruct H as [Hh|H]; [vm_compute in Hh; discriminate|].
              simpl in H.
              destruct H as [Hi|H]; [vm_compute in Hi; discriminate|].
              simpl in H.
              destruct H as [Hs|H]; [vm_compute in Hs; discriminate|].
              simpl in H.
              destruct H as [H_|H]; [vm_compute in H_; discriminate|].
              simpl in H.
              destruct H as [Hi2|H]; [vm_compute in Hi2; discriminate|].
              simpl in H.
              destruct H as [Hs2|H]; [vm_compute in Hs2; discriminate|].
              simpl in H.
              destruct H as [H_|H]; [vm_compute in H_; discriminate|].
              simpl in H.
              destruct H as [Hv|H]; [vm_compute in Hv; discriminate|].
              simpl in H.
              destruct H as [Ha|H]; [vm_compute in Ha; discriminate|].
              simpl in H.
              destruct H as [Hl|H]; [vm_compute in Hl; discriminate|].
              simpl in H.
              destruct H as [Hi3|H]; [vm_compute in Hi3; discriminate|].
              simpl in H.
              destruct H as [Hd|H]; [vm_compute in Hd; discriminate|].
              assumption.
            }
            apply Hpref in Hin1. exact Hin1.
          - assert (~ In "."%char (("t"::"x"::"t"::[])%char)) as Hsuf.
            { unfold not. intros H.
              simpl in H.
              destruct H as [Ht|H]; [vm_compute in Ht; discriminate|].
              simpl in H.
              destruct H as [Hx|H]; [vm_compute in Hx; discriminate|].
              simpl in H.
              destruct H as [Ht2|H]; [vm_compute in Ht2; discriminate|].
              assumption.
            }
            apply Hsuf in Hin2. exact Hin2.
        }
        split.
        { exists ("t"%char).
          exists (("h"::"i"::"s"::"_"::"i"::"s"::"_"::"v"::"a"::"l"::"i"::"d"::[])%char).
          split; [reflexivity|].
          unfold is_alpha. left.
          vm_compute. split; lia.
        }
        { left. reflexivity. }
  - reflexivity.
Qed.