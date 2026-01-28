Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

(* Definition: sub is a substring of main *)
Definition is_substring (sub main : list ascii) : Prop :=
  exists prefix suffix, main = prefix ++ sub ++ suffix.

(* Definition: r is a rotation of b *)
Definition is_rotation_of (r b : list ascii) : Prop :=
  exists p1 p2, b = p1 ++ p2 /\ r = p2 ++ p1.

(* Precondition *)
Definition problem_154_pre (a b : string) : Prop := True.

(* Specification *)
Definition problem_154_spec (a b : string) (res : bool) : Prop :=
  let la := list_ascii_of_string a in
  let lb := list_ascii_of_string b in
  res = true <-> (exists b', is_rotation_of b' lb /\ is_substring b' la).

(* Example Proof for input = ["xyzw"; "xyw"], output = false *)
Example test_problem_154 : problem_154_spec "xyzw" "xyw" false.
Proof.
  unfold problem_154_spec. simpl.
  split; intro H.
  - (* false = true -> ... *)
    discriminate H.
  - (* (exists b', ...) -> false = true *)
    destruct H as [b' [Hrot Hsub]].
    unfold is_rotation_of in Hrot.
    destruct Hrot as [p1 [p2 [Heq Hb']]].
    unfold is_substring in Hsub.
    destruct Hsub as [pre [suf Hsub]].
    
    (* Case analysis on p1 based on Heq: "xyw" = p1 ++ p2 *)
    destruct p1.
    + (* Case p1 = [] -> b' = "xyw" *)
      simpl in Heq. subst p2. simpl in Hb'. subst b'.
      (* Check if "xyw" is a substring of "xyzw" *)
      destruct pre; simpl in Hsub.
      * inversion Hsub. (* 'z' <> 'w' *)
      * destruct pre; simpl in Hsub.
        -- inversion Hsub. (* 'y' <> 'x' *)
        -- destruct pre; simpl in Hsub.
           ++ inversion Hsub. (* 'x' <> 'w' *)
           ++ destruct pre; simpl in Hsub; inversion Hsub.

    + destruct p1.
      * (* Case p1 = [c] -> b' = "ywx" *)
        simpl in Heq. inversion Heq. subst. simpl in Hb'. subst b'.
        (* Check if "ywx" is a substring of "xyzw" *)
        destruct pre; simpl in Hsub.
        -- inversion Hsub. (* 'x' <> 'y' *)
        -- destruct pre; simpl in Hsub.
           ++ inversion Hsub. (* 'y' <> 'w' *)
           ++ destruct pre; simpl in Hsub.
              ** inversion Hsub. (* 'z' <> 'x' *)
              ** destruct pre; simpl in Hsub; inversion Hsub.

      * destruct p1.
        -- (* Case p1 = [c1; c2] -> b' = "wxy" *)
           simpl in Heq. inversion Heq. subst. simpl in Hb'. subst b'.
           (* Check if "wxy" is a substring of "xyzw" *)
           destruct pre; simpl in Hsub.
           ++ inversion Hsub. (* 'x' <> 'w' *)
           ++ destruct pre; simpl in Hsub.
              ** inversion Hsub. (* 'y' <> 'x' *)
              ** destruct pre; simpl in Hsub.
                 --- inversion Hsub. (* 'z' <> 'y' *)
                 --- destruct pre; simpl in Hsub; inversion Hsub.

        -- destruct p1.
           ++ (* Case p1 = [c1; c2; c3] -> b' = "xyw" *)
              simpl in Heq. inversion Heq. subst. simpl in Hb'. subst b'.
              (* Check if "xyw" is a substring of "xyzw" *)
              destruct pre; simpl in Hsub.
              ** inversion Hsub.
              ** destruct pre; simpl in Hsub.
                 --- inversion Hsub.
                 --- destruct pre; simpl in Hsub.
                     +++ inversion Hsub.
                     +++ destruct pre; simpl in Hsub; inversion Hsub.
           ++ (* Case p1 has >= 4 elements *)
              simpl in Heq. inversion Heq.
Qed.