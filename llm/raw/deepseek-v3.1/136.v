
Definition largest_smallest_integers_spec (lst : list Z) (result : option Z * option Z) : Prop :=
  let neg := filter (fun x => x <? 0) lst in
  let pos := filter (fun x => x >? 0) lst in
  result = (if neg = [] then None else Some (max_list neg), 
           if pos = [] then None else Some (min_list pos)).
