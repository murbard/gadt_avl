let check_keys k = function
  | (None, None) -> true
  | (Some kl, Some kr) -> (kl < k) && (k < kr)
  | (None, Some kr) -> (k < kr)
  | (Some kl, None) -> (kl < k)
    
let rec check_node = function
  | Node n -> (match n with
      | Leaf -> (None, 0, 0)
      | Balanced {key=k;left;right;count;_} ->
        let kl, hl, cl = check_node (Node left)
        and kr, hr, cr = check_node (Node right) in
        let h, c =  (1 + max hl hr, 1 + cl + cr) in
        assert (hl = hr);
        assert (c = count);
        assert (check_keys k (kl, kr));
        (Some k, h, c)
      | LeftHeavy {key=k;left;right;count;_} ->
        let kl, hl, cl = check_node (Node left)
        and kr, hr, cr = check_node (Node right) in
        let h, c =  (1 + max hl hr, 1 + cl + cr) in
        assert (hl = hr + 1);        
        assert (c = count);
        assert (check_keys k (kl, kr));
        (Some k, h, c)
      | RightHeavy {key=k;left;right;count;_} ->
        let kl, hl, cl = check_node (Node left)
        and kr, hr, cr = check_node (Node right) in
        let h, c =  (1 + max hl hr, 1 + cl + cr) in
        assert (hl + 1 = hr);
        assert (c = count);
        assert (check_keys k (kl, kr));
        (Some k, h, c)
    )      
    
let rec tree_of_list = function
  | [] -> Node Leaf
  | h::t -> insert h (tree_of_list t)

let generate n a =
  let c = Array.init n (fun _ -> 0) in
  let p = ref [Array.to_list a] in
  let i = ref 0 in
  while !i < n do
    if c.(!i) < !i then begin
      if !i mod 2 == 0 then
        (let tmp = a.(0) in a.(0) <- a.(!i); a.(!i) <- tmp)
      else
        (let tmp = a.(c.(!i)) in a.(c.(!i)) <- a.(!i); a.(!i) <- tmp);
      p := (Array.to_list a)::(!p);
      c.(!i) <- c.(!i) + 1;
      i := 0
    end
    else begin
      c.(!i) <- 0;
      i := !i + 1
    end
  done;
  !p
  

let permut10 = generate 10 (Array.init 10 (fun i -> i))
    
let _ =
  let p = ref permut10 in
  for i = 0 to (List.length permut10) - 1 do
    print_endline (string_of_int i);
    (match (!p) with
      | l::q -> let _ = check_node (tree_of_list l) in p := q
      | [] -> assert false)
  done
      
