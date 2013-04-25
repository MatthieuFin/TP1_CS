type poly = (int*float) list;;

let p1 = [(0,2.);(1,5.);(3,1.)] ;;
let p2 = [(0,2.5);(1,5.);(2,5.);(3,1.)] ;;

let q = [(0,5.);(1,1.);(2,9.);(3,7.)];;
let r = [(0,2.);(1,4.);(2,2.)];;

let rec coeff i p = 
  match p with
      [] -> 0.
    | (deg,coef)::l when deg == i -> coef
    | e::l -> coeff i l
;;

let rec pol_is_equal p1 p2 =
  match p1, p2 with
      [], [] -> true
    | ([], _) -> false
    | (_, []) -> false
    | ((d1,c1)::l1),((d2,c2)::l2) when (d1 = d2  && c1 = c2) -> 
      (pol_is_equal l1 l2)
    | _ -> false
;;

let somme p1 p2 = 
  let rec aux p q res = 
    match p, q with
	[], [] -> List.rev res
      | [], e::rq -> aux [] rq (e::res)
      | e::rp, [] -> aux rp [] (e::res)
      | ((dp,cp)::rp), ((dq,cq)::rq) when dp < dq -> 
	aux rp q ((dp,cp)::res)
      | ((dp,cp)::rp), ((dq,cq)::rq) when dp > dq -> 
	aux p rq ((dq,cq)::res)
      | ((dp,cp)::rp), ((dq,cq)::rq) when (cp +. cq) = 0. -> 
	aux rp rq res
      | ((dp,cp)::rp), ((dq,cq)::rq) -> 
	aux rp rq ((dp,(cp +. cq))::res)
  in
  aux p1 p2 []
;;

let difference p1 p2 = 
  let rec neg p res = 
    match p with
	[] -> List.rev res
      | (dp, cp)::rp -> neg rp ((dp, (0. -. cp))::res)
  in
  somme p1 (neg p2 [])
;;

(* kara *)

let separe p n = 
  let rec aux p p1 p2 = 
    match p with
	[] -> ((List.rev p1),(List.rev p2))
      | (dp,cp)::rp -> 
	if dp < n/2
	then
	  aux rp ((dp,cp)::p1) p2
	else
	  aux rp p1 ((dp - n/2,cp)::p2)
  in
  aux p [] []
;;

let deg pol =
  let rec aux p acc =
      match p with
	  [] -> acc
	| (dp,cp)::l when dp > acc -> aux l dp
	| (dp,cp)::l -> aux l acc
  in
  aux pol 0
;;

let degPair pol = 
  let d = deg pol in
  if (d mod 2) == 0
  then
    d
  else
    d + 1
;;

let max a b = 
  if a > b
  then a
  else b
;;

let ajoutDeg p n =
  let rec aux p p1 n = match p with 
      []        -> List.rev p1
    | (d, c)::p -> aux p ((d+n, c)::p1) n
  in aux p [] n
;;

let rec mul p1 p2 =
  let n = max (degPair p1) (degPair p2) in
  if (n < 1) then
    let res = (coeff n p1) *. (coeff n p2) in
    if (res = 0.) then
      []
    else
      [(n*n,res)]
  else
    let a = (separe p1 n) and b = (separe p2 n) in
    let c0 = mul (fst a) (fst b) and
	c2 = mul (snd a) (snd b) in
    let c1 = (difference
		(difference
		   (mul 
		      (somme (fst a) (snd a))
		      (somme (fst b) (snd b)))
		   (c0))
		(c2))
    in
    (somme (somme (c0) (ajoutDeg c1 (n/2))) (ajoutDeg c2 n))
;;



(*affichage*)

let absF f =
  match f with
      i when i < 0. -> -.i
    | i when i > 0. -> i
    |_ -> 0.;;

let toString p= 
  let signe s c =
    match s, c with 
	[], i when i > 0. -> ""
      |_, i when i < 0. -> " - "
      |_, _ -> " + " 
  in
  let rec aux p acc =
    match p with
	[] -> acc
      |(d, c)::q when d = 0                             ->
	aux q acc^(signe q c)^(string_of_float (absF c))
      |(d, c)::q when (c = 1. || c = (-.1.)) && d > 1   ->
	aux q acc^(signe q c)^"x^"^(string_of_int d)
      |(d, c)::q when c < 0. && d > 1                   ->
	(aux
	  q
	  acc^(signe q c)^(string_of_float (absF c))^"x^"^(string_of_int d))
      |(d, c)::q when c > 0. && d > 1                   ->
	(aux
	  q
	  acc^(signe q c)^(string_of_float (absF c))^"x^"^(string_of_int d))
      |(d, c)::q when (c = 1.|| c = (-.1.))             ->
	aux q acc^(signe q c)^"x"
      |(d, c)::q when c < 0.                            ->
	aux q acc^(signe q c)^(string_of_float (absF c))^"x"
      |(d, c)::q when c > 0.                            ->
	aux q acc^(signe q c)^(string_of_float (absF c))^"x"
      |e::q -> aux q acc
  in
  aux p "";;

(*Division Newton*)


let renv k a =
  let rec aux p acc =
    match p with
	[] -> acc
      | (dp,cp)::l -> aux l ((k - dp,cp)::acc)
  in
  if k >= (deg a) then
    aux ( a) []
  else
    failwith "il faut k >= (deg a) !!"
;;


let pol_mod p q =
  let rec aux acc = function
  [] -> acc
    | (d,c)::l -> 
      if d < (deg q) then
	(aux ((d,c)::acc) l)
      else 
	aux acc l
  in
  aux [] (List.rev p)
;;


let gi f borne = 
  let rec aux i g =
    if (2.**i) >= borne then
      g
    else
      (aux (i+.1.)
	 (difference (mul [(0,2.)] g) (mul f (mul g g)))
      )
  in
  aux 0. [(0,1.)]
;;

gi [(0,1.);(1,1.)] 2.;;

(* split fonctionnant avec l'exemple du TD *)
let split (a : poly) (n : int) =
  let rec aux acc p =
      match p with
	  [] -> acc
	| (d,c)::l -> 
	  if d < n then
	    (aux ((d,c)::acc) l)
	  else
	    (aux acc l)
  in
  aux [] (List.rev a)
;;


let div a b =
  let m = deg a
  and n = deg b in
  let s = (gi (renv n b) (float_of_int (m - n + 1))) in
  let srA = mul s (renv m a) in
  let rQ = split srA (m-n+1)
    (*if m = n then
	split srA (m-n)
     else
	split srA (m-n+1)*)
  in
  let q = renv (m-n) rQ in
  let r = (difference a (mul b q)) in
  (q,r)
;;

(* Exemple fonctionnant avec Newton *)
let a = [(0,3.);(1,2.);(3,1.)];;
let b = [(1,1.);(2,1.)];;
toString a;;
toString b;;

let res = (div a b);;
toString (fst res);;
toString (snd res);;

(* Exemple ne fonctionnant pas avec Newton *)
let e = [0,2.];;
let f = [0,10.];;
let di = (div e f);;
toString (fst di);;
toString (snd di);;

(* test Newton *)
let x = [(0,1.);(3,1.);(4,2.);(5,3.);(7,5.)];;
let y = [(0,1.);(1,6.);(3,4.)];;
toString (x);;
toString (y);;
let d = div x y;;
toString (fst d);;
toString (snd d);;

let i = 1;;

(*  *)

let zero = [];;

let mult_coeff_poly (p : poly) (n : float) = 
  let rec loop (accu : poly) = function
    []               -> List.rev accu
    | (deg,coeff)::q -> loop ( (deg,(coeff *. n))::accu) q
  in loop [] p;;

(*
(** Pseudo-division de deux poly *)
let div2 (p1 : poly) (p2 : poly) =
  if pol_is_equal p2 zero then failwith "Division par le polynome nul."
  else
    let deg_p2 = deg p2
    and _,coeff_p2  = List.hd (List.rev p2)
    in 
    let rec loop (q : poly) (r: poly) =
      if (deg r) < (deg_p2) then (q, r)
      else 
	let q = mult_coeff_poly q coeff_p2
	and r = mult_coeff_poly r coeff_p2
	in
	let degre_div_q = (deg r) - (deg_p2)
	and coeff_div_q = (snd(List.hd (List.rev r))) /. coeff_p2
	in
	let div_q = (degre_div_q, coeff_div_q)
	in 
	let q_bis = somme q [div_q]
	and r_bis = difference r (mul [div_q] p2)
	in loop q_bis r_bis
    in loop zero p1;;
*)

let compare (p1 : poly) (p2 : poly) =
  let rec aux x y =
      match p1, p2 with
	  [],[]                              ->  0
	| [],(db,cb)::b                      -> -1
	| (da,ca)::a,[]                      ->  1
	| (da,ca)::a,(db,cb)::b when da > db ->  1
	| (da,ca)::a,(db,cb)::b when da < db -> -1
	| (da,ca)::a,(db,cb)::b when ca > cb ->  1
	| (da,ca)::a,(db,cb)::b when ca < cb -> -1
	| (da,ca)::a,(db,cb)::b              -> aux a b
  in
  aux (List.rev p1) (List.rev p2);;


let div_naiv (p1 : poly) (p2 : poly) =
  if p2 = zero then
    failwith "Division par zero !"
  else
    let rec aux (a : poly) (b : poly) (q : poly) =
      match a,b with
	  a1,b1 when (compare a1 b1) < 0 -> (q,a1)
	| a1,b1 when (compare a1 b1) = 0 -> ([0,1.],[])
	| (da,ca)::a1,(db,cb)::b1 ->
	  (aux
	    (difference a (mul [(da - db),(1.)] b) )
	    b
	    (somme q [(da - db),(1.)]))
    in
    aux p1 p2 []
;;

(*
(* Division naive. *)
  let quomod (a : poly) (b : poly) = 
    let rec aux aa k =
      if (difference aa b) = zero then
      if ((compare_gdnb (somme aa (oppose_gdnb b)) zero) < 0) then
	(k, aa)
      else
	aux (somme aa (oppose_gdnb b)) (inc k)
    in
    aux a zero;;
*)
(*let quotient_poly a b = fst(quomod_poly a b);;*)

(*  *)









let eval_poly p x = 
  let n = deg p in
  let e = (coeff n p) in
  let rec aux i acc = 
    if (i >= 0)
    then aux (i-1) ((coeff (i) p) +. x *. acc)
    else acc
  in
  aux (n-1) e
;;


(* Interpolation de Lagrange *)

(* retourne le j-eme elt d'une la liste xl *)
let elt_j j xl =
  let rec aux i l acc =
    match l with
	[] -> acc
      | e::ll when i != j-> (aux (i+1) ll e)
      | e::ll -> e
  in
  if j < 0 || j >= List.length(xl)
  then failwith "j < 0 || j >= List.length(xl)"
  else 
  (*aux 0 xl 0.*)
    (match xl with
	[]   -> failwith "liste vide !"
      | e::l -> aux 0 xl e
    )
;;




(* Arrondi un flottant proche de 0 a 0 et un flottant proche de 1 a 1 avec 
   une approximation de approx *)
let arrondi f = 
  let approx = 0.000001 in
  if (f >= 0. && (f -. approx) < 0.)
  then 0.
  else
    if (f <= 0. && (f +. approx) > 0.)
    then 0.
    else 
      if (f >= 1. && (f -. approx) < 1.)
      then 1.
      else 
	if (f <= 1. && (f +. approx) > 1.)
	then 1.
	else f
;;




(* xl de la forme [x0; x1; x2; x3; x4; ...] *)

(* p1 est de degré 1 et p2 est de degré 0*)
let div_float p1 p2 = 
  if deg p1 != 1 || deg p2 != 0
  then
    failwith "deg p1 != 1 || deg p2 != 0"
  else 
    [(0,((coeff 0 p1)/.(eval_poly p2 0.)));
     (1,((coeff 1 p1)/.(eval_poly p2 0.)))]
;;


(* xl de la forme [x0; x1; x2; x3; x4; ...] *)
let li i xl = 
  let rec aux j acc = 
    if j >= 0
    then 
      (aux (j-1)
         (if j != i
	  then 
	     (mul 
		acc
		(div_float 
		   (difference ([1,1.]) ([0,(fst (elt_j j xl))]))
		   (difference 
		      ([0,(fst (elt_j i xl))])
		      ([0,(fst (elt_j j xl))])))
	     )
	  else 
	     (acc)
	 )
      )
    else acc
  in
  aux ((List.length xl) - 1) [0,1.]
;;


(* ptsL : liste de points de la forme [(x0,y0); (x1,y1); (x2,y2); ...]*)
let interpol ptsL = 
  let rec aux i acc = 
    if i >= 0
    then aux (i-1)
             (somme 
		(acc) 
		(mul ([0,(snd (elt_j i ptsL))]) ((li i ptsL)))
	     )
    else acc
  in
  aux ((List.length ptsL) - 1) [(0,0.)]
;;

let p = [(1,(-12.)/.40.);(2,19./.40.);(3,(-8.)/.40.);(4,1./.40.)];;
eval_poly p 1.;;
let lx = [(-1.,3.);(0.,1.);(1.,2.);(3.,-1.);(4.,-5.)];;
interpol lx;;
toString (interpol lx);;

let lq3 = [(-5.,2.);(-3.,4.);(-1.,8.);(1.,8.);(3.,4.);(5.,2.)];;
interpol lq3;;
toString (interpol lq3);;

let interpol_arr ptsL =
  let rec aux l acc = 
    match l with
	[] -> acc
      | (d,c)::ll -> let arr = (arrondi c) in
		     if (arr = 0.)
		     then aux ll acc
		     else aux ll [(d, arr)]@acc
		       
  in
  aux (List.rev (interpol ptsL)) []
;;

let fonction x = 64./.(x*.x +. 7.);;

interpol lq3;;
interpol_arr lq3;;


#load "graphics.cma";;
open Graphics ;;

let xmin = 0 and ymin = 0;;
let xmax = 800;;
let ymax = 400;;
let xori = xmax/2;;
let yori = ymax/2;;

open_graph (" "^string_of_int(xmax)^"x"^string_of_int(ymax));;

let drawing f zoom xorigine yorigine = 
  let pas = 0.5 
  (*and zoom = 5. *)
  in
  let rec aux x = 
    if x < (float_of_int (size_x ())) /. 2.
    then 
      let useless = (lineto 
		       ((int_of_float (x *. zoom)) + xorigine)
		       ((int_of_float ((f x) *. zoom)) + yorigine)
                    ) in
      (aux (x +. pas))
    else 
  moveto xorigine yorigine
  in
  aux (float_of_int (xorigine - (size_x ())))
;;

let draw_x_unit x zoom xorigine yorigine = 
  moveto (x * zoom + xorigine) (yorigine-5);
  lineto (x * zoom + xorigine) (yorigine+5)
;;
let draw_y_unit y zoom xorigine yorigine = 
  moveto (xorigine-5) (y * zoom + yorigine);
  lineto (xorigine+5) (y * zoom + yorigine)
;;

let draw_reper zoom xorigine yorigine = 
  set_color black;
  moveto 0 yorigine;
  lineto (size_x ()) yorigine;
  moveto xorigine 0;
  lineto xorigine (size_y ());
  (*  *)
  
  let rec aux x unit =
    if x < (size_x ())
    then 
      aux (x+1) ((draw_x_unit x zoom) xorigine yorigine )
    else 
      moveto 0 0
  in
  aux (((-1 * xmax)/(zoom*2))) () ;
  let rec auy y unit =
    if (y*zoom) < (size_y ())
    then 
      auy (y+1) ((draw_y_unit y zoom) xorigine yorigine )
    else 
      moveto 0 0
  in
  auy (((-1 * ymax)/(zoom*2))) ();
    (*  *)
  moveto ((size_x ())- 15) (yorigine + 10);
  draw_char 'x';
  moveto (xorigine + 10) ((size_y ())- 15);
  draw_char 'y';
  moveto (xorigine - 10) (yorigine - 15);
  draw_char 'O';
  moveto xorigine yorigine;
;;

let draw f color zoom xorigine yorigine =
  (*let zoom = 20. in*)
  (*draw_reper (int_of_float zoom) xorigine yorigine ;*)
  set_color color;
  let xdep = ((xorigine - (size_x ()))) in
  moveto xdep (int_of_float (f (float_of_int xdep)));
  drawing f zoom xorigine yorigine;
  set_color black;
;;

let rec loop k zoom f1 f2 xorigine yorigine = 
  if k = 'q' || k = '\027'
  then close_graph ()
  else 
    if k = '-'
    then 
      if zoom > 1.
	then
	let a = clear_graph ()
	and b = draw (f1) (red) (zoom -. 1.) xorigine yorigine
	and c = draw (f2) green (zoom -. 1.) xorigine yorigine
	and d = draw_reper (int_of_float zoom) xorigine yorigine
	in
	loop (read_key ()) (zoom -. 1.) f1 f2 xorigine yorigine
      else loop (read_key ()) (zoom) f1 f2 xorigine yorigine
    else 
      if k = '+'
      then
	let a = clear_graph ()
	and b = draw (f1) (red) (zoom +. 1.) xorigine yorigine
	and c = draw (f2) green (zoom +. 1.) xorigine yorigine
	and d = draw_reper (int_of_float zoom) xorigine yorigine
	in
	loop (read_key ()) (zoom +. 1.) f1 f2 xorigine yorigine
      else 
	if k = 'l'
	then
	  let a = clear_graph ()
	  and b = draw (f1) (red) (zoom) (xorigine - 10) yorigine
	  and c = draw (f2) green (zoom) (xorigine - 10) yorigine
	  and d = draw_reper (int_of_float zoom) (xorigine - 10) yorigine
	  in
	  loop (read_key ()) (zoom) f1 f2 (xorigine - 10) yorigine
	else 
	  if k = 'j'
	  then
	    let a = clear_graph ()
	    and b = draw (f1) (red) (zoom) (xorigine + 10) yorigine
	    and c = draw (f2) green (zoom) (xorigine + 10) yorigine
	    and d = draw_reper (int_of_float zoom) (xorigine + 10) yorigine
	    in
	    loop (read_key ()) (zoom) f1 f2 (xorigine + 10) yorigine
	  else 
	    if k = 'k'
	    then
	      let a = clear_graph ()
	      and b = draw (f1) (red) (zoom) xorigine (yorigine + 10)
	      and c = draw (f2) green (zoom) xorigine (yorigine + 10)
	      and d = 
		draw_reper 
		  (int_of_float zoom) xorigine (yorigine + 10)
	      in
	      loop (read_key ()) (zoom) f1 f2 xorigine (yorigine + 10)
	    else 
	      if k = 'i'
	      then
		let a = clear_graph ()
		and b = draw (f1) (red) (zoom) xorigine (yorigine - 10)
		and c = draw (f2) green (zoom) xorigine (yorigine - 10)
		and d = 
		  draw_reper (int_of_float zoom) xorigine (yorigine - 10)
		in

		loop (read_key ()) (zoom) f1 f2 xorigine (yorigine - 10)
	      else loop (read_key ()) (zoom) f1 f2 xorigine yorigine
;;

let f1 = fonction;;
let f2 = eval_poly (interpol_arr lq3);;


draw (fonction) (red) (20.) xori yori;;
draw (eval_poly (interpol_arr lq3)) green 20. xori yori;;
draw_reper (int_of_float 20.) xori yori;;
loop (read_key ()) (20.) f1 f2 xori yori;;


(*
arrondi (eval_poly (li 0 lx) (fst (elt_j 0 lx)));;
arrondi (eval_poly (li 0 lx) (fst (elt_j 1 lx)));;
arrondi (eval_poly (li 0 lx) (fst (elt_j 2 lx)));;
arrondi (eval_poly (li 0 lx) (fst (elt_j 3 lx)));;
arrondi (eval_poly (li 0 lx) (fst (elt_j 4 lx)));;

arrondi (eval_poly (li 1 lx) (fst (elt_j 0 lx)));;
arrondi (eval_poly (li 1 lx) (fst (elt_j 1 lx)));;
arrondi (eval_poly (li 1 lx) (fst (elt_j 2 lx)));;
arrondi (eval_poly (li 1 lx) (fst (elt_j 3 lx)));;
arrondi (eval_poly (li 1 lx) (fst (elt_j 4 lx)));;

arrondi (eval_poly (li 2 lx) (fst (elt_j 0 lx)));;
arrondi (eval_poly (li 2 lx) (fst (elt_j 1 lx)));;
arrondi (eval_poly (li 2 lx) (fst (elt_j 2 lx)));;
arrondi (eval_poly (li 2 lx) (fst (elt_j 3 lx)));;
arrondi (eval_poly (li 2 lx) (fst (elt_j 4 lx)));;

arrondi (eval_poly (li 3 lx) (fst (elt_j 0 lx)));;
arrondi (eval_poly (li 3 lx) (fst (elt_j 1 lx)));;
arrondi (eval_poly (li 3 lx) (fst (elt_j 2 lx)));;
arrondi (eval_poly (li 3 lx) (fst (elt_j 3 lx)));;
arrondi (eval_poly (li 3 lx) (fst (elt_j 4 lx)));;

arrondi (eval_poly (li 4 lx) (fst (elt_j 0 lx)));;
arrondi (eval_poly (li 4 lx) (fst (elt_j 1 lx)));;
arrondi (eval_poly (li 4 lx) (fst (elt_j 2 lx)));;
arrondi (eval_poly (li 4 lx) (fst (elt_j 3 lx)));;
arrondi (eval_poly (li 4 lx) (fst (elt_j 4 lx)));;
*)

(*
mul q r;;

let a = [(0,3.);(1,2.);(3,1.)];;
let b = [(1,1.);(2,1.)];;

pol_mod (renv 2 b) [(2,1.)];;

div a b;;
*)
