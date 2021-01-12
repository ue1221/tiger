structure Semant : SEMANT =
struct
	structure A = Absyn
	structure E = Env
	structure S = Symbol
	structure T = Types

	val error = ErrorMsg.error

	type venv = E.enventry S.table
	type tenv = E.ty S.table
	type expty = {exp: Translate.exp, ty: T.ty}

	fun actual_ty (tenv, ty, pos) = case ty of
		T.NAME (sym, nameTy) => (case !nameTy of
			NONE => (case S.look (tenv, sym) of
				NONE => (error pos ("undefined type " ^ S.name sym); T.NIL)
				| SOME (ty') => actual_ty (tenv, ty', pos)
			)
			| SOME (ty') => actual_ty (tenv, ty', pos)
		)
		| T.ARRAY (ty', uniq) => T.ARRAY (actual_ty (tenv, ty', pos), uniq)
		| _ => ty

	fun checkInt ({exp, ty}, pos) = case ty of
		T.INT => ()
		| _ => error pos "expected an integer"

	fun checkString ({exp, ty}, pos) = case ty of
		T.STRING => ()
		| _ => error pos "expected a string"

	fun checkRecord ({exp, ty}, pos) = case ty of
		T.RECORD (_) => ()
		| _ => error pos "expected a record"

	fun checkArray ({exp, ty}, pos) = case ty of
		T.ARRAY (_) => ()
		| _ => error pos "expected an array"

	fun checkUnit ({exp, ty}, pos) = case ty of
		T.UNIT => ()
		| _ => error pos "expected an unit"

	fun checkTypes (ty1, ty2, pos) =
		if ty1 = T.NIL then
			case ty2 of
				(T.NIL | T.RECORD (_) | T.ARRAY (_)) => ()
				| _ => error pos "incompatible types"
		else if ty2 = T.NIL then
			case ty1 of
				(T.NIL | T.RECORD (_) | T.ARRAY (_)) => ()
				| _ => error pos "incompatible types"
		else if ty1 = ty2 then
			()
		else
			error pos "incompatible types"

	val tmpExpty = {exp = (), ty = T.NIL}

	fun transVar (venv, tenv, var) =
	let
		fun trvar (A.SimpleVar (sym, pos)) = (case S.look (venv, sym) of
			NONE => (error pos ("undefined function " ^ S.name sym); tmpExpty)
			| SOME (E.FunEntry _) => (error pos "expected a variable"; tmpExpty)
			| SOME (E.VarEntry {ty}) =>  {exp = (), ty = actual_ty (tenv, ty, pos)}
		)
		| trvar (A.FieldVar (var, sym, pos)) =
		let
			val {exp = _, ty = ty} = trvar var
		in
			case ty of
				T.RECORD (namelist, uniq) => (
					case List.find (fn (sym', ty') => sym' = sym) namelist of
						SOME (sym', ty') => {exp = (), ty = actual_ty (tenv, ty, pos)}
						| NONE => (error pos ("undefined field " ^ S.name sym); tmpExpty)
				)
				| _ => (error pos "expected a record"; tmpExpty)
		end
		| trvar (A.SubscriptVar (var, exp, pos)) =
		let
			val {exp = _, ty = varTy} = trvar var
			val expExpty = transExp (venv, tenv, exp)
		in
			case varTy of
				T.ARRAY (ty, uniq) => (
					checkInt (expExpty, pos);
					{exp = (), ty = actual_ty (tenv, ty, pos)}
				)
				| _ => (error pos "expected an array"; tmpExpty)
		end
	in
		trvar var
	end

	and transExp (venv, tenv, exp) =
	let
		fun trexp (A.VarExp var) = transVar (venv, tenv, var)
		| trexp (A.NilExp) = {exp = (), ty = T.NIL}
		| trexp (A.IntExp _) = {exp = (), ty = T.INT}
		| trexp (A.StringExp _) = {exp = (), ty = T.STRING}
		| trexp (A.CallExp {func, args, pos}) = (case S.look (venv, func) of
			NONE => (error pos ("undefined function " ^ S.name func); tmpExpty)
			| SOME (E.VarEntry _) => (error pos "expected a function"; tmpExpty)
			| SOME (E.FunEntry {formals, result}) => (
				let
					val argnum = length args
					fun check (arg: A.exp, formal: E.ty) =
					let
						val {exp = (), ty = argTy} = trexp arg
					in
						checkTypes (argTy, formal, pos)
					end
				in
					if argnum <> (length formals) then
						(error pos "wrong number of arguments"; tmpExpty)
					else
						(app check (ListPair.zip (args, formals)); {exp = (), ty = result})
				end
			)
		)
		| trexp (A.OpExp {left, oper, right, pos}) =
		let
			val leftExpty = trexp left
			val rightExpty = trexp right
			val {exp = _, ty = leftTy} = leftExpty
		in
			case oper of
				(A.PlusOp | A.MinusOp | A.TimesOp | A.DivideOp) => (
					checkInt (leftExpty, pos);
					checkInt (rightExpty, pos);
					{exp = (), ty = T.INT}
				)
				| (A.LtOp | A.LeOp | A.GtOp | A.GeOp) => (
					case leftTy of
						T.INT => checkInt (rightExpty, pos)
						| T.STRING => checkString (rightExpty, pos)
						| _ => error pos "unexpected type";
					{exp = (), ty = T.INT}
				)
				| (A.EqOp | A.NeqOp) => (
					case leftTy of
						T.INT => checkInt (rightExpty, pos)
						| T.STRING => checkString (rightExpty, pos)
						| T.RECORD (_) => checkRecord (rightExpty, pos)
						| T.ARRAY (_) => checkArray (rightExpty, pos)
						| _ => error pos "unexpected type";
					{exp = (), ty = T.INT}
				)
		end
		| trexp (A.RecordExp {fields, typ, pos}) = (case S.look (tenv, typ) of
			NONE => (error pos ("undefined type " ^ S.name typ); tmpExpty)
			| SOME (recordTy) => (
				let
					val actualTy = actual_ty (tenv, recordTy, pos)
				in
					case actualTy of
						T.RECORD (namelist, uniq) => (
							let
								fun check ((sym1, exp, pos), (sym2, ty2)) =
									if sym1 = sym2 then
										let
											val {exp = _, ty = ty1} = trexp exp
										in
											checkTypes (ty1, ty2, pos)
										end
									else
										error pos "incompatible symbols"
							in
								app check (ListPair.zip (fields, namelist));
								{exp = (), ty = T.RECORD (namelist, uniq)}
							end
						)
						| _ => (error pos ("unexpected type"); tmpExpty)
				end
			)
		)
		| trexp (A.SeqExp expseq) = (
			if List.null (expseq) then
				tmpExpty
			else
				let
					val (explist, poslist) = ListPair.unzip expseq
					val exptylist = map trexp explist
					val {exp = _, ty = lastTy} = List.last exptylist
				in
					{exp = (), ty = lastTy}
				end
		)
		| trexp (A.AssignExp {var, exp, pos}) =
		let
			val {exp = _, ty = varTy} = transVar (venv, tenv, var)
			val {exp = _, ty = expTy} = trexp exp
		in
			checkTypes (varTy, expTy, pos);
			{exp = (), ty = T.UNIT}
		end
		| trexp (A.IfExp {test, then', else', pos}) =
		let
			val testExpty = trexp test
			val thenExpty = trexp then'
			val elseExpty = case else' of
				NONE => {exp = (), ty = T.UNIT}
				| SOME (else'') => trexp else''
			val {exp = _, ty = thenTy} = thenExpty
			val {exp = _, ty = elseTy} = elseExpty
		in
			checkInt (testExpty, pos);
			checkTypes (thenTy, elseTy, pos);
			{exp = (), ty = thenTy}
		end
		| trexp (A.WhileExp {test, body, pos}) =
		let
			val testExpty = trexp test
			val bodyExpty = trexp body
		in
			checkInt (testExpty, pos);
			checkUnit (bodyExpty, pos);
			{exp = (), ty = T.UNIT}
		end
		| trexp (A.ForExp {var, escape, lo, hi, body, pos}) =
		let
			val loExpty = trexp lo
			val hiExpty = trexp hi
			val venv' = S.enter (venv, var, E.VarEntry {ty = T.INT})
			val bodyExpty = transExp (venv', tenv, body)
		in
			checkInt (loExpty, pos);
			checkInt (hiExpty, pos);
			checkUnit (bodyExpty, pos);
			{exp = (), ty = T.UNIT}
		end
		| trexp (A.BreakExp pos) = {exp = (), ty = T.UNIT}
		| trexp (A.LetExp {decs, body, pos}) =
		let
			fun trdecs (venv, tenv, []) = {venv = venv, tenv = tenv}
			| trdecs (venv, tenv, dec :: decs) =
			let
				val {venv = venv', tenv = tenv'} = transDec (venv, tenv, dec)
			in
				trdecs (venv', tenv', decs)
			end
			val {venv = venv', tenv = tenv'} = trdecs (venv, tenv, decs)
		in
			transExp (venv', tenv', body)
		end
		| trexp (A.ArrayExp {typ, size, init, pos}) = case S.look (tenv, typ) of
			NONE => (error pos ("undefined type " ^ S.name typ); tmpExpty)
			| SOME (arratTy) => (
				let
					val actualTy = actual_ty (tenv, arratTy, pos)
				in
					case actualTy of
						T.ARRAY (ty, uniq) =>
						let
							val sizeExpty = trexp size
							val {exp = _, ty = initTy} = trexp init
						in
							checkInt (sizeExpty, pos);
							checkTypes (ty, initTy, pos);
							{exp = (), ty = T.ARRAY (ty, uniq)}
						end
						| _ => (error pos ("unexpected type"); tmpExpty)
				end
			)
	in
		trexp exp
	end

	and transDec (venv, tenv, dec) =
	let
		fun trdec (A.FunctionDec fundecs) =
		let
			fun getResultTy (result) = case result of
				NONE => T.UNIT
				| SOME (typ, pos) => (case S.look (tenv, typ) of
					SOME (t) => t
					| NONE => (error pos ("undefined type " ^ S.name typ); T.NIL)
				)
			fun toFunEntry ({name, params, result, body, pos}) =
			let
				val resultTy = getResultTy result
				val formals =
				let
					fun getty ({name, escape, typ, pos}) = case S.look (tenv, typ) of
						SOME (t) => t
						| NONE => (error pos ("undefined type " ^ S.name typ); T.NIL)
				in
					map getty params
				end
			in
				(name, E.FunEntry {formals = formals, result = resultTy})
			end
			val venv' =
			let
				fun enter ((name, funentry), venv) = S.enter (venv, name, funentry)
			in
				List.foldl enter venv (map toFunEntry fundecs)
			end
			fun trfundec ({name, params, result, body, pos}) =
			let
				val resultTy = getResultTy result
				val venv'' =
				let
					fun enter ({name, escape, typ, pos}, venv) =
					let
						val ty = case S.look (tenv, typ) of
							SOME (t) => t
							| NONE => (error pos ("undefined type " ^ S.name typ); T.NIL)
					in
						S.enter (venv, name, E.VarEntry {ty = ty})
					end
				in
					List.foldl enter venv' params
				end
				val {exp = _, ty = bodyTy} = transExp (venv', tenv, body)
			in
				checkTypes (bodyTy, resultTy, pos)
			end
		in
			{venv = venv', tenv = tenv}
		end
		| trdec (A.VarDec vardec) =
		let
			val {name, escape, typ, init, pos} = vardec
			val {exp = _, ty = initTy} = transExp (venv, tenv, init)
		in
			case typ of
				NONE => {venv = S.enter (venv, name, E.VarEntry {ty = initTy}), tenv = tenv}
				| SOME (sym, pos) => (case S.look (tenv, sym) of
					NONE => (
						("undefined type " ^ S.name sym);
						{venv = S.enter (venv, name, E.VarEntry {ty = initTy}), tenv = tenv}
					)
					| SOME (t) => 
						let
							val actualTy = actual_ty (tenv, t, pos)
						in
							checkTypes (initTy, actualTy, pos);
							{venv = S.enter (venv, name, E.VarEntry {ty = initTy}), tenv = tenv}
						end
				)
		end
		| trdec (A.TypeDec tydecs) =
		let
			val tenv' = 
			let
				fun enter ({name, ty, pos}, tenv) = S.enter (tenv, name, T.NAME (name, ref NONE))
			in
				List.foldl enter tenv tydecs
			end
			val tenv'' = 
			let
				fun enter ({name, ty, pos}, tenv) = (
					(case S.look (tenv, name) of
						SOME (T.NAME (name', ref')) => (
							ref' := SOME (transTy (tenv, ty))
						)
						| _ => ()
					);
					tenv
				)
			in
				List.foldl enter tenv' tydecs
			end
			fun checkCycle (seen, next, pos) = case next of
				NONE => (error pos ("undefined type"); false)
				| SOME (t) => (case t of
					T.NAME (sym, ty) => (
						if (List.all (fn (e) => e <> sym) seen) then
							checkCycle (sym :: seen, !ty, pos)
						else
							false
					)
					| _ => true
				)
			fun check (nil) = ()
			| check ({name, ty, pos} :: tydecs) = case S.look (tenv'', name) of
				SOME (T.NAME (_, ty')) => (
					if checkCycle ([name], !ty', pos) then
						check (tydecs)
					else
						error pos ("cyclic definition " ^ S.name name)
				)
				| _ => ()
		in
			check (tydecs);
			{venv = venv, tenv = tenv''}
		end
	in
		trdec dec
	end

	and transTy (tenv, ty) =
	let
		fun trty (A.NameTy (sym, pos)) = T.NAME (sym, ref (S.look (tenv, sym)))
		| trty (A.RecordTy (fields)) =
		let
			fun toNamelist ({name, escape, typ, pos}) = case S.look (tenv, typ) of
				SOME (t) => (name, t)
				| NONE => (error pos ("undefined type " ^ S.name typ); (name, T.NIL))
		in
			T.RECORD (map toNamelist fields, ref ())
		end
		| trty (A.ArrayTy (sym, pos)) = (case S.look(tenv,sym) of
			SOME (t) => T.ARRAY (t, ref ())
			| NONE => (error pos ("undefined type " ^ S.name sym); T.NIL)
		)
	in
		trty ty
	end

	and transProg (exp) = (transExp (E.base_venv, E.base_tenv, exp); ())
end