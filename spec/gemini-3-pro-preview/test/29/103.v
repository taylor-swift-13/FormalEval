Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Import ListNotations.
Open Scope string_scope.

Definition filter_by_prefix_spec (strings : list string) (pref : string) (result : list string) : Prop :=
  result = filter (fun s => prefix pref s) strings.

Fixpoint bytes_to_string (l : list nat) : string :=
  match l with
  | [] => EmptyString
  | n :: t => String (ascii_of_nat n) (bytes_to_string t)
  end.

Definition s_dian := bytes_to_string [231; 148; 181].
Definition s_dianying := bytes_to_string [231; 148; 181; 229; 189; 177].
Definition s_dianzi := bytes_to_string [231; 148; 181; 229; 173; 144].
Definition s_dianhua := bytes_to_string [231; 148; 181; 232; 175; 157].
Definition s_youjian := bytes_to_string [233; 130; 174; 228; 187; 182].

Example test_filter_by_prefix_chinese : 
  filter_by_prefix_spec [s_dianying; s_dianzi; s_dianhua; s_youjian] s_dian [s_dianying; s_dianzi; s_dianhua].
Proof.
  unfold filter_by_prefix_spec.
  vm_compute.
  reflexivity.
Qed.