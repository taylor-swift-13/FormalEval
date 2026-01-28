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

Example problem_141_test_no_one_knows_dll :
  problem_141_spec "no_one#knows.dll"%string "Yes"%string.
Proof.
  unfold problem_141_spec.
  simpl.
  left. split.
  - split.
    + vm_compute. lia.
    + exists (("n"::"o"::"_"::"o"::"n"::"e"::"#"::"k"::"n"::"o"::"w"::"s"::[])%char).
      exists (("d"::"l"::"l"::[])%char).
      split.
      * vm_compute. reflexivity.
      * split.
        { intro HIn.
          apply in_app_iff in HIn.
          destruct HIn as [Hin1|Hin2].
          - assert (~ In "."%char (("n"::"o"::"_"::"o"::"n"::"e"::"#"::"k"::"n"::"o"::"w"::"s"::[])%char)) as Hpref.
            { unfold not. intros H.
              simpl in H.
              destruct H as [Hn|H]; [vm_compute in Hn; discriminate|].
              simpl in H.
              destruct H as [Ho|H]; [vm_compute in Ho; discriminate|].
              simpl in H.
              destruct H as [Hu|H]; [vm_compute in Hu; discriminate|].
              simpl in H.
              destruct H as [Ho2|H]; [vm_compute in Ho2; discriminate|].
              simpl in H.
              destruct H as [Hn2|H]; [vm_compute in Hn2; discriminate|].
              simpl in H.
              destruct H as [He|H]; [vm_compute in He; discriminate|].
              simpl in H.
              destruct H as [Hh|H]; [vm_compute in Hh; discriminate|].
              simpl in H.
              destruct H as [Hk|H]; [vm_compute in Hk; discriminate|].
              simpl in H.
              destruct H as [Hn3|H]; [vm_compute in Hn3; discriminate|].
              simpl in H.
              destruct H as [Ho3|H]; [vm_compute in Ho3; discriminate|].
              simpl in H.
              destruct H as [Hw|H]; [vm_compute in Hw; discriminate|].
              simpl in H.
              destruct H as [Hs|H]; [vm_compute in Hs; discriminate|].
              contradiction.
            }
            apply Hpref in Hin1. contradiction.
          - assert (~ In "."%char (("d"::"l"::"l"::[])%char)) as Hsuf.
            { unfold not. intros H.
              simpl in H.
              destruct H as [Hd|H]; [vm_compute in Hd; discriminate|].
              simpl in H.
              destruct H as [Hl|H]; [vm_compute in Hl; discriminate|].
              simpl in H.
              destruct H as [Hl2|H]; [vm_compute in Hl2; discriminate|].
              contradiction.
            }
            apply Hsuf in Hin2. contradiction.
        }
        split.
        { exists ("n"%char).
          exists (("o"::"_"::"o"::"n"::"e"::"#"::"k"::"n"::"o"::"w"::"s"::[])%char).
          split; [reflexivity|].
          unfold is_alpha. left.
          vm_compute. split; lia.
        }
        { right. right. reflexivity. }
  - reflexivity.
Qed.