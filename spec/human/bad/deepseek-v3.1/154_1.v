Require Import Coq.Lists.List.
Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Import ListNotations.

Fixpoint list_ascii_of_string (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s' => c :: list_ascii_of_string s'
  end.

Definition is_substring (sub main : list ascii) : Prop :=
  exists prefix suffix, main = prefix ++ sub ++ suffix.

Definition is_rotation_of (r b : list ascii) : Prop :=
  exists p1 p2, b = p1 ++ p2 /\ r = p2 ++ p1.

Definition problem_154_spec (a b : string) (res : bool) : Prop :=
  let la := list_ascii_of_string a in
  let lb := list_ascii_of_string b in
  res = true <-> (exists b', is_rotation_of b' lb /\ is_substring b' la).

Example test_case_xyzw_xyw_false : 
  problem_154_spec "xyzw" "xyw" false.
Proof.
  unfold problem_154_spec.
  simpl.
  split.
  - intros H. discriminate H.
  - intros H. 
    destruct H as [b' [Hrot Hsub]].
    unfold is_rotation_of in Hrot.
    destruct Hrot as [p1 [p2 [Heq1 Heq2]]].
    
    (* Case analysis on the length of p1 for the 3-character string "xyw" *)
    destruct p1 as [|c1 p1'].
    + (* Case 1: p1 is empty *)
      simpl in Heq1, Heq2.
      (* p2 must be "xyw" *)
      destruct p2 as [|c2 p2'].
      * simpl in Heq1. discriminate.
      * destruct p2' as [|c3 p2''].
        -- simpl in Heq1. discriminate.
        -- destruct p2'' as [|c4 p2'''].
           ++ simpl in Heq1. discriminate.
           ++ simpl in Heq1, Heq2.
              (* Now check if "xyw" is substring of "xyzw" *)
              unfold is_substring in Hsub.
              destruct Hsub as [prefix [suffix Heq]].
              simpl in Heq.
              (* Try all possible prefix lengths *)
              destruct prefix as [|p prefix'].
              ** simpl in Heq.
                 (* Check if "xyw" appears at beginning *)
                 destruct suffix as [|s suffix'].
                 --- simpl in Heq. discriminate.  (* "xyw" ≠ "xyzw" *)
                 --- simpl in Heq. discriminate.  (* "xyw" ≠ "x" ++ "xyw" ++ rest *)
              ** destruct prefix' as [|p' prefix''].
                 --- simpl in Heq. discriminate.  (* "y" ++ "xyw" ++ rest =?= "xyzw" *)
                 --- destruct prefix'' as [|p'' prefix'''].
                     +++ simpl in Heq. discriminate.  (* "z" ++ "xyw" ++ rest =?= "xyzw" *)
                     +++ simpl in Heq. discriminate.  (* too long *)
    + (* Case 2: p1 has at least one character *)
      destruct p1' as [|c2 p1''].
      * (* p1 has exactly one character *)
        simpl in Heq1, Heq2.
        destruct p2 as [|c3 p2'].
        -- simpl in Heq1. discriminate.
        -- destruct p2' as [|c4 p2''].
           ++ simpl in Heq1. discriminate.
           ++ simpl in Heq1, Heq2.
              (* Rotation is "ywx" *)
              unfold is_substring in Hsub.
              destruct Hsub as [prefix [suffix Heq]].
              simpl in Heq.
              (* Try all possible prefix lengths *)
              destruct prefix as [|p prefix'].
              ** simpl in Heq.
                 destruct suffix as [|s suffix'].
                 --- simpl in Heq. discriminate.  (* "ywx" ≠ "xyzw" *)
                 --- simpl in Heq. discriminate.
              ** destruct prefix' as [|p' prefix''].
                 --- simpl in Heq. discriminate.  (* "y" ++ "ywx" ++ rest =?= "xyzw" *)
                 --- destruct prefix'' as [|p'' prefix'''].
                     +++ simpl in Heq. discriminate.  (* "z" ++ "ywx" ++ rest =?= "xyzw" *)
                     +++ simpl in Heq. discriminate.
      + (* Case 3: p1 has at least two characters *)
        destruct p1'' as [|c3 p1'''].
        * (* p1 has exactly two characters *)
          simpl in Heq1, Heq2.
          destruct p2 as [|c4 p2'].
          -- simpl in Heq1. discriminate.
          -- simpl in Heq1, Heq2.
             (* Rotation is "wxy" *)
             unfold is_substring in Hsub.
             destruct Hsub as [prefix [suffix Heq]].
             simpl in Heq.
             (* Try all possible prefix lengths *)
             destruct prefix as [|p prefix'].
             ** simpl in Heq.
                destruct suffix as [|s suffix'].
                --- simpl in Heq. discriminate.  (* "wxy" ≠ "xyzw" *)
                --- simpl in Heq. discriminate.
             ** destruct prefix' as [|p' prefix''].
                --- simpl in Heq. discriminate.  (* "y" ++ "wxy" ++ rest =?= "xyzw" *)
                --- destruct prefix'' as [|p'' prefix'''].
                    +++ simpl in Heq. discriminate.  (* "z" ++ "wxy" ++ rest =?= "xyzw" *)
                    +++ simpl in Heq. discriminate.
        * (* p1 has three or more characters - impossible for "xyw" *)
          simpl in Heq1. discriminate.
Qed.