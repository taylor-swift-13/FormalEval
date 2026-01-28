Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Import ListNotations.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Definition char (n : nat) : ascii := ascii_of_nat n.

(* Construct UTF-8 string "电" (bytes 231 148 181) *)
Definition s_dian : string := 
  String (char 231) (String (char 148) (String (char 181) EmptyString)).

(* Construct UTF-8 string "影" (bytes 229 189 177) *)
Definition s_ying : string :=
  String (char 229) (String (char 189) (String (char 177) EmptyString)).

(* Construct "电影" by appending "电" and "影" *)
Definition s_dianying : string := append s_dian s_ying.

Example test_filter_by_prefix_dian : filter_by_prefix_spec [s_dianying] s_dian [s_dianying].
Proof.
  unfold filter_by_prefix_spec.
  simpl.
  reflexivity.
Qed.