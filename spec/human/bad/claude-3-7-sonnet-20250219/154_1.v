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
  exists p1 p2 : list ascii, b = p1 ++ p2 /\ r = p2 ++ p1.

Definition problem_154_pre (a b : string) : Prop := True.

Definition problem_154_spec (a b : string) (res : bool) : Prop :=
  let la := list_ascii_of_string a in
  let lb := list_ascii_of_string b in
  res = true <-> (exists b', is_rotation_of b' lb /\ is_substring b' la).

Example problem_154_test_case : problem_154_spec "xyzw" "xyw" false.
Proof.
  unfold problem_154_spec.
  simpl.
  split.
  - intros H. discriminate H.
  - intros [b' [Hrot Hsub]].
    unfold is_rotation_of in Hrot.
    destruct Hrot as [p1 [p2 [Hb Hr]]].
    unfold is_substring in Hsub.
    destruct Hsub as [prefix [suffix Hmain]].
    subst.
    (* We have:
       la = prefix ++ (p2 ++ p1) ++ suffix
       lb = p1 ++ p2 = [x; y; w]
       r = p2 ++ p1
       la = [x; y; z; w]
    *)
    (* Lengths:
       length lb = 3
       length la = 4
    *)

    (* From Hb: [x;y;w] = p1 ++ p2 *)
    (* length (p1 ++ p2) = 3 *)
    rewrite app_length in Hb.
    assert (Hlen_len: length p1 + length p2 = 3) by (rewrite Hb; reflexivity).

    (* From Hmain: la = prefix ++ (p2 ++ p1) ++ suffix *)
    rewrite app_assoc in Hmain.
    rewrite app_length in Hmain.
    assert (Hlen_main: length prefix + length p2 + length p1 + length suffix = length la) by (rewrite Hmain; reflexivity).
    simpl in Hlen_main.
    rewrite <- !plus_assoc in Hlen_main.

    (* length la = 4 *)
    assert (Hlen_la: length la = 4) by reflexivity.
    rewrite Hlen_la in Hlen_main.

    (* Substitute length p1 + length p2 = 3 *)
    rewrite Hlen_len in Hlen_main.

    (* So length prefix + 3 + length suffix = 4 *)
    (* Hence, length prefix + length suffix = 1 *)
    assert (Hpre_suf: length prefix + length suffix = 1) by lia.

    (* Try to show contradiction because substring (rotation r) of length 3 found in length 4 with prefix + suffix =1 *)

    (* We analyze possible prefixes and suffixes of length sum 1 *)

    (* The possible cases: prefix length = 0 and suffix length =1, or prefix length=1 and suffix length=0 *)

    destruct prefix as [|p cprefix].
    + (* prefix length = 0 *)
      (* suffix length = 1 *)
      destruct suffix as [|s csuffix].
      * (* suffix length = 0 contradicts prefix+suffix=1 *)
        lia.
      * (* suffix length =1 *)
        (* So la = (p2 ++ p1) ++ suffix *)
        subst la.
        simpl in Hmain.
        (* la = (p2 ++ p1) ++ suffix *)
        assert (Hla_eq: [ "x"%char; "y"%char; "z"%char; "w"%char ] = p2 ++ p1 ++ s :: csuffix) by assumption.

        (* length (p2 ++ p1) = 3, suffix length = 1 *)

        (* We can try to check whether p2 ++ p1 ++ suffix = la is possible *)

        (* Compare heads of la and p2 ++ p1 ++ suffix *)
        (* la starts with x *)
        destruct p2 as [|c1 p2'].
        -- (* p2 = [] *)
           simpl in Hla_eq.
           rewrite app_nil_l in Hla_eq.
           destruct p1 as [|c2 p1']; simpl in *.
           ++ discriminate.
           ++ inversion Hla_eq.
              subst.
              (* Then la = c2 :: p1' ++ s :: csuffix = x :: y :: z :: w :: nil *)
              (* length mismatch *)
              lia.
        -- (* p2 = c1 :: p2' *)
           simpl in Hla_eq.
           (* la = c1 :: p2' ++ p1 ++ s :: csuffix *)
           (* la = [x; y; z; w] *)
           inversion Hla_eq; subst; clear Hla_eq.
           (* So c1 = x *)
           (* [y; z; w] = p2' ++ p1 ++ s :: csuffix *)

           (* length of [y; z; w] = 3 *)
           (* length of p2' + length p1 + 1 = 3 *)
           rewrite app_length in *.
           simpl in *.
           lia.
    + (* prefix length = 1 *)
      destruct suffix as [|s csuffix].
      * (* suffix length = 0 *)
        (* sum prefix+suffix=1 *)
        subst la.
        simpl in Hmain.
        (* la = prefix ++ p2 ++ p1 ++ [] = prefix ++ p2 ++ p1 *)
        (* la = [x; y; z; w] *)

        (* prefix = p :: cprefix *)
        simpl in Hmain.
        (* So p :: cprefix ++ p2 ++ p1 = la *)

        (* p :: (cprefix ++ p2 ++ p1) = la *)

        (* So head p = x *)
        inversion Hmain; subst; clear Hmain.

        (* We have cprefix ++ p2 ++ p1 = [y; z; w] *)

        (* length cprefix + length p2 + length p1 = 3 *)

        rewrite app_length in *.
        simpl in *.
        lia.
      * (* suffix length ≥ 1 contradicts prefix + suffix = 1 *)
        simpl in Hpre_suf.
        lia.
Qed.