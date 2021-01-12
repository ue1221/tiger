structure Env: ENV = 
struct
	structure S = Symbol
	structure T = Types

	type access = unit (* TODO *)
	type ty = T.ty

	datatype enventry
		= VarEntry of {ty: ty}
		| FunEntry of {formals: ty list, result: ty}

	val builtintypelist = [
		("int", T.INT),
		("string", T.STRING)
	]

	val builtinfunclist = [
		("print", FunEntry {formals = [T.STRING], result = T.UNIT}),
		("flush", FunEntry {formals = [], result = T.UNIT}),
		("getchar", FunEntry {formals = [], result = T.STRING}),
		("ord", FunEntry {formals = [T.STRING], result = T.INT}),
		("chr", FunEntry {formals = [T.INT], result = T.STRING}),
		("size", FunEntry {formals = [T.STRING], result = T.INT}),
		("substring", FunEntry {formals = [T.STRING, T.INT, T.INT], result = T.STRING}),
		("concat", FunEntry {formals = [T.STRING, T.STRING], result = T.STRING}),
		("not", FunEntry {formals = [T.INT], result = T.INT}),
		("exit", FunEntry {formals = [T.INT], result = T.UNIT})
	]

	val base_tenv =
	let
		fun enter ((name, ty), tenv) = S.enter (tenv, S.symbol name, ty)
	in
		List.foldr enter S.empty builtintypelist
	end

	val base_venv =
	let
		fun enter ((name, enventry), venv) = S.enter (venv, S.symbol name, enventry)
	in
		List.foldr enter S.empty builtinfunclist
	end
end