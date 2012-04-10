functor MLLexFun(structure Tokens : ML_TOKENS)  = struct

    structure yyInput : sig

        type stream
	val mkStream : (int -> string) -> stream
	val fromStream : TextIO.StreamIO.instream -> stream
	val getc : stream -> (Char.char * stream) option
	val getpos : stream -> int
	val getlineNo : stream -> int
	val subtract : stream * stream -> string
	val eof : stream -> bool
	val lastWasNL : stream -> bool

      end = struct

        structure TIO = TextIO
        structure TSIO = TIO.StreamIO
	structure TPIO = TextPrimIO

        datatype stream = Stream of {
            strm : TSIO.instream,
	    id : int,  (* track which streams originated 
			* from the same stream *)
	    pos : int,
	    lineNo : int,
	    lastWasNL : bool
          }

	local
	  val next = ref 0
	in
	fun nextId() = !next before (next := !next + 1)
	end

	val initPos = 2 (* ml-lex bug compatibility *)

	fun mkStream inputN = let
              val strm = TSIO.mkInstream 
			   (TPIO.RD {
			        name = "lexgen",
				chunkSize = 4096,
				readVec = SOME inputN,
				readArr = NONE,
				readVecNB = NONE,
				readArrNB = NONE,
				block = NONE,
				canInput = NONE,
				avail = (fn () => NONE),
				getPos = NONE,
				setPos = NONE,
				endPos = NONE,
				verifyPos = NONE,
				close = (fn () => ()),
				ioDesc = NONE
			      }, "")
	      in 
		Stream {strm = strm, id = nextId(), pos = initPos, lineNo = 1,
			lastWasNL = true}
	      end

	fun fromStream strm = Stream {
		strm = strm, id = nextId(), pos = initPos, lineNo = 1, lastWasNL = true
	      }

	fun getc (Stream {strm, pos, id, lineNo, ...}) = (case TSIO.input1 strm
              of NONE => NONE
	       | SOME (c, strm') => 
		   SOME (c, Stream {
			        strm = strm', 
				pos = pos+1, 
				id = id,
				lineNo = lineNo + 
					 (if c = #"\n" then 1 else 0),
				lastWasNL = (c = #"\n")
			      })
	     (* end case*))

	fun getpos (Stream {pos, ...}) = pos

	fun getlineNo (Stream {lineNo, ...}) = lineNo

	fun subtract (new, old) = let
	      val Stream {strm = strm, pos = oldPos, id = oldId, ...} = old
	      val Stream {pos = newPos, id = newId, ...} = new
              val (diff, _) = if newId = oldId andalso newPos >= oldPos
			      then TSIO.inputN (strm, newPos - oldPos)
			      else raise Fail 
				"BUG: yyInput: attempted to subtract incompatible streams"
	      in 
		diff 
	      end

	fun eof s = not (isSome (getc s))

	fun lastWasNL (Stream {lastWasNL, ...}) = lastWasNL

      end

    datatype yystart_state = 
A | F | L | Q | S | AQ | LL | LLC | LLCQ | INITIAL
    structure UserDeclarations = 
      struct

(* ml.lex
 *
 * Copyright 1989 by AT&T Bell Laboratories
 *)

open ErrorMsg;

structure TokTable = TokenTable(Tokens);
type svalue = Tokens.svalue
type pos = int
type lexresult = (svalue,pos) Tokens.token
type lexarg = {
	comLevel : int ref, 
	sourceMap : SourceMap.sourcemap,
	charlist : string list ref,
	stringtype : bool ref,
	stringstart : int ref, (* start of current string or comment*)
	brack_stack : int ref list ref, (* for frags *)
	err : pos*pos -> ErrorMsg.complainer
      }
type arg = lexarg
type ('a,'b) token = ('a,'b) Tokens.token
fun eof ({comLevel,err,charlist,stringstart,sourceMap, ...} : lexarg) = let
      val pos = Int.max(!stringstart+2, SourceMap.lastLinePos sourceMap)
      in
	if !comLevel>0
	  then err (!stringstart,pos) COMPLAIN "unclosed comment" nullErrorBody
          else if !charlist <> []
            then err (!stringstart,pos) COMPLAIN
                  "unclosed string, character, or quotation" nullErrorBody

	    else ();
	Tokens.EOF(pos,pos)
      end	
fun addString (charlist,s:string) = charlist := s :: (!charlist)
fun addChar (charlist, c:char) = addString(charlist, String.str c)
fun makeString charlist = (concat(rev(!charlist)) before charlist := nil)

local
  fun cvt radix (s, i) =
	#1(valOf(IntInf.scan radix Substring.getc (Substring.triml i (Substring.full s))))
in
val atoi = cvt StringCvt.DEC
val xtoi = cvt StringCvt.HEX
end (* local *)

fun mysynch (srcmap, initpos, pos, args) =
    let fun cvt digits = getOpt(Int.fromString digits, 0)
	val resynch = SourceMap.resynch srcmap
     in case args
          of [col, line] => 
	       resynch (initpos, pos, cvt line, cvt col, NONE)
           | [file, col, line] => 
	       resynch (initpos, pos, cvt line, cvt col, SOME file)
           | _ => impossible "ill-formed args in (*#line...*)"
    end

fun has_quote s =
    let fun loop i = ((String.sub(s,i) = #"`") orelse loop (i+1))
	             handle _ => false
     in loop 0
    end

fun inc (ri as ref i) = (ri := i+1)
fun dec (ri as ref i) = (ri := i-1)


      end

    datatype yymatch 
      = yyNO_MATCH
      | yyMATCH of yyInput.stream * action * yymatch
    withtype action = yyInput.stream * yymatch -> UserDeclarations.lexresult

    local

    val yytable = 
#[([(#"\^@",#"\t",10),
(#"\v",#"\f",10),
(#"\^N",#"'",10),
(#")",#")",10),
(#"+",#"\255",10),
(#"\n",#"\n",11),
(#"\r",#"\r",12),
(#"(",#"(",13),
(#"*",#"*",14)], []), ([(#"\^@",#"\b",17),
(#"\v",#"\v",17),
(#"\^N",#"\^_",17),
(#"!",#"[",17),
(#"]",#"\255",17),
(#"\t",#"\t",18),
(#"\f",#"\f",18),
(#" ",#" ",18),
(#"\n",#"\n",19),
(#"\r",#"\r",20),
(#"\\",#"\\",21)], [69]), ([(#"\^@",#"\t",23),
(#"\v",#")",23),
(#"+",#"/",23),
(#":",#"\255",23),
(#"*",#"*",24),
(#"0",#"9",25)], []), ([(#"\^@",#"\t",28),
(#"\v",#"\f",28),
(#"\^N",#"]",28),
(#"_",#"_",28),
(#"a",#"\255",28),
(#"\n",#"\n",29),
(#"\r",#"\r",30),
(#"^",#"^",31),
(#"`",#"`",32)], []), ([(#"\^@",#"\t",35),
(#"\v",#"\f",35),
(#"\^N",#"\^_",35),
(#"\n",#"\n",36),
(#"\r",#"\r",37),
(#" ",#" ",38),
(#"\127",#"\255",38),
(#"!",#"!",39),
(#"#",#"[",39),
(#"]",#"~",39),
(#"\"",#"\"",40),
(#"\\",#"\\",41)], []), ([(#"\^@",#"\b",62),
(#"\v",#"\v",62),
(#"\^N",#"\^_",62),
(#"\"",#"\"",62),
(#"'",#"'",62),
(#")",#")",62),
(#",",#",",62),
(#".",#".",62),
(#"0",#"9",62),
(#";",#";",62),
(#"[",#"[",62),
(#"]",#"]",62),
(#"_",#"`",62),
(#"{",#"{",62),
(#"}",#"}",62),
(#"\127",#"\255",62),
(#"\t",#"\t",63),
(#"\f",#"\f",63),
(#" ",#" ",63),
(#"\n",#"\n",64),
(#"\r",#"\r",65),
(#"!",#"!",66),
(#"#",#"&",66),
(#"*",#"+",66),
(#"-",#"-",66),
(#"/",#"/",66),
(#":",#":",66),
(#"<",#"@",66),
(#"\\",#"\\",66),
(#"^",#"^",66),
(#"|",#"|",66),
(#"~",#"~",66),
(#"(",#"(",67),
(#"A",#"Z",68),
(#"a",#"z",68)], [79]), ([(#".",#".",72),
(#"0",#"0",73),
(#"1",#"9",74)], [38]), ([(#"\^@",#"\b",23),
(#"\v",#"\v",23),
(#"\r",#"\^_",23),
(#"!",#"!",23),
(#"#",#")",23),
(#"+",#"\255",23),
(#"\t",#"\t",75),
(#"\f",#"\f",75),
(#" ",#" ",75),
(#"\"",#"\"",76),
(#"*",#"*",77)], []), ([(#"\^@",#"\t",81),
(#"\v",#"!",81),
(#"#",#")",81),
(#"+",#"\255",81),
(#"\n",#"\n",82),
(#"\"",#"\"",83),
(#"*",#"*",84)], [41]), ([(#"\^@",#"\b",88),
(#"\v",#"\v",88),
(#"\^N",#"\^_",88),
(#"\127",#"\255",88),
(#"\t",#"\t",89),
(#"\f",#"\f",89),
(#" ",#" ",89),
(#"\n",#"\n",90),
(#"\r",#"\r",91),
(#"!",#"!",92),
(#"$",#"&",92),
(#"+",#"+",92),
(#"-",#"-",92),
(#"/",#"/",92),
(#":",#":",92),
(#"<",#"@",92),
(#"\\",#"\\",92),
(#"^",#"^",92),
(#"|",#"|",92),
(#"\"",#"\"",93),
(#"#",#"#",94),
(#"'",#"'",95),
(#"(",#"(",96),
(#")",#")",97),
(#"*",#"*",98),
(#",",#",",99),
(#".",#".",100),
(#"0",#"0",101),
(#"1",#"9",102),
(#";",#";",103),
(#"A",#"Z",104),
(#"a",#"g",104),
(#"i",#"z",104),
(#"[",#"[",105),
(#"]",#"]",106),
(#"_",#"_",107),
(#"`",#"`",108),
(#"h",#"h",109),
(#"{",#"{",110),
(#"}",#"}",111),
(#"~",#"~",112)], [0]), ([], [48]), ([], [46]), ([(#"\n",#"\n",11)], [46, 48]), ([(#"*",#"*",16)], [48]), ([(#")",#")",15)], [48]), ([], [47]), ([], [45]), ([], [71]), ([(#"\t",#"\t",22),
(#"\f",#"\f",22),
(#" ",#" ",22)], [69, 71]), ([], [68]), ([(#"\n",#"\n",19)], [68, 71]), ([], [70, 71]), ([(#"\t",#"\t",22),
(#"\f",#"\f",22),
(#" ",#" ",22)], [69]), ([], [44]), ([(#")",#")",27)], [44]), ([(#"0",#"9",26)], [35, 44]), ([(#"0",#"9",26)], [35]), ([], [43]), ([], [77]), ([], [76]), ([(#"\n",#"\n",29)], [76, 77]), ([(#"^",#"^",33),
(#"`",#"`",34)], [74, 77]), ([], [75, 77]), ([], [73]), ([], [72]), ([], [66, 67]), ([], [50, 66]), ([(#"\n",#"\n",61)], [50, 66, 67]), ([], [67]), ([(#"!",#"!",60),
(#"#",#"[",60),
(#"]",#"~",60)], [67]), ([], [49, 67]), ([(#"\t",#"\t",42),
(#"\f",#"\f",42),
(#" ",#" ",42),
(#"\n",#"\n",43),
(#"\r",#"\r",44),
(#"\"",#"\"",45),
(#"0",#"9",46),
(#"\\",#"\\",47),
(#"^",#"^",48),
(#"a",#"a",49),
(#"b",#"b",50),
(#"f",#"f",51),
(#"n",#"n",52),
(#"r",#"r",53),
(#"t",#"t",54),
(#"v",#"v",55)], [52, 65, 67]), ([(#"\t",#"\t",42),
(#"\f",#"\f",42),
(#" ",#" ",42)], [52]), ([], [51]), ([(#"\n",#"\n",43)], [51]), ([], [61]), ([(#"0",#"9",58)], []), ([], [60]), ([(#"\^@",#"\t",56),
(#"\v",#"?",56),
(#"`",#"\255",56),
(#"@",#"_",57)], []), ([], [53]), ([], [54]), ([], [55]), ([], [56]), ([], [57]), ([], [58]), ([], [59]), ([], [63]), ([], [62, 63]), ([(#"0",#"9",59)], []), ([], [64]), ([(#"!",#"!",60),
(#"#",#"[",60),
(#"]",#"~",60)], [67]), ([], [50]), ([], [83]), ([(#"\t",#"\t",71),
(#"\f",#"\f",71),
(#" ",#" ",71)], [79, 83]), ([], [78]), ([(#"\n",#"\n",64)], [78, 83]), ([(#"!",#"!",70),
(#"#",#"&",70),
(#"*",#"+",70),
(#"-",#"-",70),
(#"/",#"/",70),
(#":",#":",70),
(#"<",#"@",70),
(#"\\",#"\\",70),
(#"^",#"^",70),
(#"|",#"|",70),
(#"~",#"~",70)], [81, 83]), ([], [82, 83]), ([(#"'",#"'",69),
(#"0",#"9",69),
(#"A",#"Z",69),
(#"_",#"_",69),
(#"a",#"z",69)], [80, 83]), ([(#"'",#"'",69),
(#"0",#"9",69),
(#"A",#"Z",69),
(#"_",#"_",69),
(#"a",#"z",69)], [80]), ([(#"!",#"!",70),
(#"#",#"&",70),
(#"*",#"+",70),
(#"-",#"-",70),
(#"/",#"/",70),
(#":",#":",70),
(#"<",#"@",70),
(#"\\",#"\\",70),
(#"^",#"^",70),
(#"|",#"|",70),
(#"~",#"~",70)], [81]), ([(#"\t",#"\t",71),
(#"\f",#"\f",71),
(#" ",#" ",71)], [79]), ([], [36]), ([(#"0",#"0",73),
(#"1",#"9",74)], [37, 38]), ([(#"0",#"9",74)], [37]), ([(#"\t",#"\t",79),
(#"\f",#"\f",79),
(#" ",#" ",79),
(#"\"",#"\"",80)], [44]), ([], [40, 44]), ([(#")",#")",78)], [44]), ([], [39, 43]), ([(#"\t",#"\t",79),
(#"\f",#"\f",79),
(#" ",#" ",79),
(#"\"",#"\"",80)], []), ([], [40]), ([(#"\^@",#"!",82),
(#"#",#"\255",82)], [41, 44]), ([(#"\^@",#"!",82),
(#"#",#"\255",82)], [41]), ([(#"*",#"*",86)], [44]), ([(#"\^@",#"!",82),
(#"#",#"(",82),
(#"*",#"\255",82),
(#")",#")",85)], [41, 44]), ([(#"\^@",#"!",82),
(#"#",#"\255",82)], [41, 43]), ([(#")",#")",87)], []), ([], [42]), ([], [34]), ([(#"\t",#"\t",157),
(#"\f",#"\f",157),
(#" ",#" ",157)], [0, 34]), ([], [1]), ([(#"\n",#"\n",90)], [1, 34]), ([(#"!",#"!",113),
(#"#",#"&",113),
(#"*",#"+",113),
(#"-",#"-",113),
(#"/",#"/",113),
(#":",#":",113),
(#"<",#"@",113),
(#"\\",#"\\",113),
(#"^",#"^",113),
(#"|",#"|",113),
(#"~",#"~",113),
(#"`",#"`",116)], [17, 18, 34]), ([], [28, 34]), ([(#"!",#"!",113),
(#"#",#"&",113),
(#"*",#"+",113),
(#"-",#"-",113),
(#"/",#"/",113),
(#":",#":",113),
(#"<",#"@",113),
(#"\\",#"\\",113),
(#"^",#"^",113),
(#"|",#"|",113),
(#"~",#"~",113),
(#"\"",#"\"",155),
(#"[",#"[",156),
(#"`",#"`",116)], [17, 18, 34]), ([(#"'",#"'",151),
(#"0",#"9",152),
(#"A",#"Z",153),
(#"a",#"z",153),
(#"_",#"_",154)], [34]), ([(#"*",#"*",144)], [11, 34]), ([], [12, 34]), ([(#"!",#"!",113),
(#"#",#"&",113),
(#"*",#"+",113),
(#"-",#"-",113),
(#"/",#"/",113),
(#":",#":",113),
(#"<",#"@",113),
(#"\\",#"\\",113),
(#"^",#"^",113),
(#"|",#"|",113),
(#"~",#"~",113),
(#")",#")",143),
(#"`",#"`",116)], [17, 18, 34]), ([], [4, 34]), ([(#".",#".",141)], [13, 34]), ([(#".",#".",117),
(#"0",#"9",134),
(#"E",#"E",118),
(#"e",#"e",118),
(#"w",#"w",135),
(#"x",#"x",136)], [22, 34]), ([(#".",#".",117),
(#"0",#"9",133),
(#"E",#"E",118),
(#"e",#"e",118)], [21, 22, 34]), ([], [10, 34]), ([(#"'",#"'",124),
(#"0",#"9",124),
(#"A",#"Z",124),
(#"_",#"_",124),
(#"a",#"z",124)], [16, 34]), ([], [7, 34]), ([], [9, 34]), ([(#"o",#"o",125)], [3, 34]), ([(#"!",#"!",116),
(#"#",#"&",116),
(#"*",#"+",116),
(#"-",#"-",116),
(#"/",#"/",116),
(#":",#":",116),
(#"<",#"@",116),
(#"\\",#"\\",116),
(#"^",#"^",116),
(#"`",#"`",116),
(#"|",#"|",116),
(#"~",#"~",116)], [17, 19, 34]), ([(#"'",#"'",124),
(#"0",#"9",124),
(#"A",#"Z",124),
(#"_",#"_",124),
(#"a",#"z",124)], [16, 33, 34]), ([], [5, 34]), ([], [6, 34]), ([(#"!",#"!",113),
(#"#",#"&",113),
(#"*",#"+",113),
(#"-",#"-",113),
(#"/",#"/",113),
(#":",#":",113),
(#"<",#"@",113),
(#"\\",#"\\",113),
(#"^",#"^",113),
(#"|",#"|",113),
(#"~",#"~",113),
(#"0",#"0",114),
(#"1",#"9",115),
(#"`",#"`",116)], [17, 18, 34]), ([(#"!",#"!",113),
(#"#",#"&",113),
(#"*",#"+",113),
(#"-",#"-",113),
(#"/",#"/",113),
(#":",#":",113),
(#"<",#"@",113),
(#"\\",#"\\",113),
(#"^",#"^",113),
(#"|",#"|",113),
(#"~",#"~",113),
(#"`",#"`",116)], [17, 18]), ([(#".",#".",117),
(#"0",#"9",115),
(#"E",#"E",118),
(#"e",#"e",118),
(#"x",#"x",122)], [23]), ([(#".",#".",117),
(#"0",#"9",115),
(#"E",#"E",118),
(#"e",#"e",118)], [23]), ([(#"!",#"!",116),
(#"#",#"&",116),
(#"*",#"+",116),
(#"-",#"-",116),
(#"/",#"/",116),
(#":",#":",116),
(#"<",#"@",116),
(#"\\",#"\\",116),
(#"^",#"^",116),
(#"`",#"`",116),
(#"|",#"|",116),
(#"~",#"~",116)], [17]), ([(#"0",#"9",121)], []), ([(#"0",#"9",119),
(#"~",#"~",120)], []), ([(#"0",#"9",119)], [20]), ([(#"0",#"9",119)], []), ([(#"0",#"9",121),
(#"E",#"E",118),
(#"e",#"e",118)], [20]), ([(#"0",#"9",123),
(#"A",#"F",123),
(#"a",#"f",123)], []), ([(#"0",#"9",123),
(#"A",#"F",123),
(#"a",#"f",123)], [25]), ([(#"'",#"'",124),
(#"0",#"9",124),
(#"A",#"Z",124),
(#"_",#"_",124),
(#"a",#"z",124)], [16]), ([(#"v",#"v",126)], []), ([(#"e",#"e",127)], []), ([(#"r",#"r",128)], []), ([(#"l",#"l",129)], []), ([(#"o",#"o",130)], []), ([(#"a",#"a",131)], []), ([(#"d",#"d",132)], []), ([], [2]), ([(#".",#".",117),
(#"0",#"9",133),
(#"E",#"E",118),
(#"e",#"e",118)], [21, 22]), ([(#".",#".",117),
(#"0",#"9",134),
(#"E",#"E",118),
(#"e",#"e",118)], [22]), ([(#"0",#"9",138),
(#"x",#"x",139)], []), ([(#"0",#"9",137),
(#"A",#"F",137),
(#"a",#"f",137)], []), ([(#"0",#"9",137),
(#"A",#"F",137),
(#"a",#"f",137)], [24]), ([(#"0",#"9",138)], [26]), ([(#"0",#"9",140),
(#"A",#"F",140),
(#"a",#"f",140)], []), ([(#"0",#"9",140),
(#"A",#"F",140),
(#"a",#"f",140)], [27]), ([(#".",#".",142)], []), ([], [14]), ([], [32]), ([(#"#",#"#",145)], [31]), ([(#"l",#"l",146)], []), ([(#"i",#"i",147)], []), ([(#"n",#"n",148)], []), ([(#"e",#"e",149)], []), ([(#"\t",#"\t",150),
(#"\f",#"\f",150),
(#" ",#" ",150)], []), ([(#"\t",#"\t",150),
(#"\f",#"\f",150),
(#" ",#" ",150)], [30]), ([(#"0",#"9",152),
(#"A",#"Z",153),
(#"a",#"z",153),
(#"_",#"_",154)], []), ([(#"0",#"9",152),
(#"A",#"Z",153),
(#"a",#"z",153)], []), ([(#"'",#"'",153),
(#"0",#"9",153),
(#"A",#"Z",153),
(#"_",#"_",153),
(#"a",#"z",153)], [15]), ([(#"A",#"Z",153),
(#"a",#"z",153)], []), ([], [29]), ([], [8]), ([(#"\t",#"\t",157),
(#"\f",#"\f",157),
(#" ",#" ",157)], [0])]
    fun mk yyins = let
        (* current start state *)
        val yyss = ref INITIAL
	fun YYBEGIN ss = (yyss := ss)
	(* current input stream *)
        val yystrm = ref yyins
	(* get one char of input *)
	val yygetc = yyInput.getc
	(* create yytext *)
	fun yymktext(strm) = yyInput.subtract (strm, !yystrm)
        open UserDeclarations
        fun lex 
(yyarg as ({
  comLevel,
  sourceMap,
  err,
  charlist,
  stringstart,
  stringtype,
  brack_stack})) () = let 
     fun continue() = let
            val yylastwasn = yyInput.lastWasNL (!yystrm)
            fun yystuck (yyNO_MATCH) = raise Fail "stuck state"
	      | yystuck (yyMATCH (strm, action, old)) = 
		  action (strm, old)
	    val yypos = yyInput.getpos (!yystrm)
	    val yygetlineNo = yyInput.getlineNo
	    fun yyactsToMatches (strm, [],	  oldMatches) = oldMatches
	      | yyactsToMatches (strm, act::acts, oldMatches) = 
		  yyMATCH (strm, act, yyactsToMatches (strm, acts, oldMatches))
	    fun yygo actTable = 
		(fn (~1, _, oldMatches) => yystuck oldMatches
		  | (curState, strm, oldMatches) => let
		      val (transitions, finals') = Vector.sub (yytable, curState)
		      val finals = map (fn i => Vector.sub (actTable, i)) finals'
		      fun tryfinal() = 
		            yystuck (yyactsToMatches (strm, finals, oldMatches))
		      fun find (c, []) = NONE
			| find (c, (c1, c2, s)::ts) = 
		            if c1 <= c andalso c <= c2 then SOME s
			    else find (c, ts)
		      in case yygetc strm
			  of SOME(c, strm') => 
			       (case find (c, transitions)
				 of NONE => tryfinal()
				  | SOME n => 
				      yygo actTable
					(n, strm', 
					 yyactsToMatches (strm, finals, oldMatches)))
			   | NONE => tryfinal()
		      end)
	    in 
let
fun yyAction0 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction1 (strm, lastMatch : yymatch) = (yystrm := strm;
      (SourceMap.newline sourceMap yypos; continue()))
fun yyAction2 (strm, lastMatch : yymatch) = let
      val oldStrm = !(yystrm)
      fun REJECT () = (yystrm := oldStrm; yystuck(lastMatch))
      in
        yystrm := strm;
        (if !ParserControl.overloadKW then
                             Tokens.OVERLOAD(yypos,yypos+1)
                         else REJECT())
      end
fun yyAction3 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.WILD(yypos,yypos+1)))
fun yyAction4 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.COMMA(yypos,yypos+1)))
fun yyAction5 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LBRACE(yypos,yypos+1)))
fun yyAction6 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.RBRACE(yypos,yypos+1)))
fun yyAction7 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.LBRACKET(yypos,yypos+1)))
fun yyAction8 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.VECTORSTART(yypos,yypos+1)))
fun yyAction9 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.RBRACKET(yypos,yypos+1)))
fun yyAction10 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.SEMICOLON(yypos,yypos+1)))
fun yyAction11 (strm, lastMatch : yymatch) = (yystrm := strm;
      (if (null(!brack_stack))
                    then ()
                    else inc (hd (!brack_stack));
                    Tokens.LPAREN(yypos,yypos+1)))
fun yyAction12 (strm, lastMatch : yymatch) = (yystrm := strm;
      (if (null(!brack_stack))
                    then ()
                    else if (!(hd (!brack_stack)) = 1)
                         then ( brack_stack := tl (!brack_stack);
                                charlist := [];
                                YYBEGIN Q)
                         else dec (hd (!brack_stack));
                    Tokens.RPAREN(yypos,yypos+1)))
fun yyAction13 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DOT(yypos,yypos+1)))
fun yyAction14 (strm, lastMatch : yymatch) = (yystrm := strm;
      (Tokens.DOTDOTDOT(yypos,yypos+3)))
fun yyAction15 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (TokTable.checkTyvar(yytext,yypos))
      end
fun yyAction16 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (TokTable.checkId(yytext, yypos))
      end
fun yyAction17 (strm, lastMatch : yymatch) = let
      val oldStrm = !(yystrm)
      fun REJECT () = (yystrm := oldStrm; yystuck(lastMatch))
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (if !ParserControl.quotation
                            then if (has_quote yytext)
                                 then REJECT()
                                 else TokTable.checkSymId(yytext,yypos)
                            else TokTable.checkSymId(yytext,yypos))
      end
fun yyAction18 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (TokTable.checkSymId(yytext,yypos))
      end
fun yyAction19 (strm, lastMatch : yymatch) = (yystrm := strm;
      (if !ParserControl.quotation
                            then (YYBEGIN Q;
                                  charlist := [];
                                  Tokens.BEGINQ(yypos,yypos+1))
                            else (err(yypos, yypos+1)
                                     COMPLAIN "quotation implementation error"
				     nullErrorBody;
                                  Tokens.BEGINQ(yypos,yypos+1))))
fun yyAction20 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.REAL(yytext,yypos,yypos+size yytext))
      end
fun yyAction21 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.INT(atoi(yytext, 0),yypos,yypos+size yytext))
      end
fun yyAction22 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.INT0(atoi(yytext, 0),yypos,yypos+size yytext))
      end
fun yyAction23 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.INT0(atoi(yytext, 0),yypos,yypos+size yytext))
      end
fun yyAction24 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.INT0(xtoi(yytext, 2),yypos,yypos+size yytext))
      end
fun yyAction25 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (Tokens.INT0(IntInf.~(xtoi(yytext, 3)),yypos,yypos+size yytext))
      end
fun yyAction26 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.WORD(atoi(yytext, 2),yypos,yypos+size yytext))
      end
fun yyAction27 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (Tokens.WORD(xtoi(yytext, 3),yypos,yypos+size yytext))
      end
fun yyAction28 (strm, lastMatch : yymatch) = (yystrm := strm;
      (charlist := [""]; stringstart := yypos;
                    stringtype := true; YYBEGIN S; continue()))
fun yyAction29 (strm, lastMatch : yymatch) = (yystrm := strm;
      (charlist := [""]; stringstart := yypos;
                    stringtype := false; YYBEGIN S; continue()))
fun yyAction30 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN L; stringstart := yypos; comLevel := 1; continue()))
fun yyAction31 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN A; stringstart := yypos; comLevel := 1; continue()))
fun yyAction32 (strm, lastMatch : yymatch) = (yystrm := strm;
      (err (yypos,yypos+1) COMPLAIN "unmatched close comment"
		        nullErrorBody;
		    continue()))
fun yyAction33 (strm, lastMatch : yymatch) = (yystrm := strm;
      (err (yypos,yypos) COMPLAIN "non-Ascii character"
		        nullErrorBody;
		    continue()))
fun yyAction34 (strm, lastMatch : yymatch) = (yystrm := strm;
      (err (yypos,yypos) COMPLAIN "illegal token" nullErrorBody;
		    continue()))
fun yyAction35 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (YYBEGIN LL; charlist := [yytext]; continue())
      end
fun yyAction36 (strm, lastMatch : yymatch) = (yystrm := strm;
      ((* cheat: take n > 0 dots *) continue()))
fun yyAction37 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (YYBEGIN LLC; addString(charlist, yytext); continue())
      end
fun yyAction38 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN LLC; addString(charlist, "1");    continue()
		(* note hack, since ml-lex chokes on the empty string for 0* *)))
fun yyAction39 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN INITIAL; mysynch(sourceMap, !stringstart, yypos+2, !charlist); 
		              comLevel := 0; charlist := []; continue()))
fun yyAction40 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN LLCQ; continue()))
fun yyAction41 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (addString(charlist, yytext); continue())
      end
fun yyAction42 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN INITIAL; mysynch(sourceMap, !stringstart, yypos+3, !charlist); 
		              comLevel := 0; charlist := []; continue()))
fun yyAction43 (strm, lastMatch : yymatch) = (yystrm := strm;
      (err (!stringstart, yypos+1) WARN 
                       "ill-formed (*#line...*) taken as comment" nullErrorBody;
                     YYBEGIN INITIAL; comLevel := 0; charlist := []; continue()))
fun yyAction44 (strm, lastMatch : yymatch) = (yystrm := strm;
      (err (!stringstart, yypos+1) WARN 
                       "ill-formed (*#line...*) taken as comment" nullErrorBody;
                     YYBEGIN A; continue()))
fun yyAction45 (strm, lastMatch : yymatch) = (yystrm := strm;
      (inc comLevel; continue()))
fun yyAction46 (strm, lastMatch : yymatch) = (yystrm := strm;
      (SourceMap.newline sourceMap yypos; continue()))
fun yyAction47 (strm, lastMatch : yymatch) = (yystrm := strm;
      (dec comLevel; if !comLevel=0 then YYBEGIN INITIAL else (); continue()))
fun yyAction48 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction49 (strm, lastMatch : yymatch) = (yystrm := strm;
      (let val s = makeString charlist
                        val s = if size s <> 1 andalso not(!stringtype)
                                 then (err(!stringstart,yypos) COMPLAIN
                                      "character constant not length 1"
                                       nullErrorBody;
                                       substring(s^"x",0,1))
                                 else s
                        val t = (s,!stringstart,yypos+1)
                    in YYBEGIN INITIAL;
                       if !stringtype then Tokens.STRING t else Tokens.CHAR t
                    end))
fun yyAction50 (strm, lastMatch : yymatch) = (yystrm := strm;
      (err (!stringstart,yypos) COMPLAIN "unclosed string"
		        nullErrorBody;
		    SourceMap.newline sourceMap yypos;
		    YYBEGIN INITIAL; Tokens.STRING(makeString charlist,!stringstart,yypos)))
fun yyAction51 (strm, lastMatch : yymatch) = (yystrm := strm;
      (SourceMap.newline sourceMap (yypos+1);
		    YYBEGIN F; continue()))
fun yyAction52 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN F; continue()))
fun yyAction53 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist, "\007"); continue()))
fun yyAction54 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist, "\008"); continue()))
fun yyAction55 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist, "\012"); continue()))
fun yyAction56 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist, "\010"); continue()))
fun yyAction57 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist, "\013"); continue()))
fun yyAction58 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist, "\009"); continue()))
fun yyAction59 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist, "\011"); continue()))
fun yyAction60 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist, "\\"); continue()))
fun yyAction61 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist, "\""); continue()))
fun yyAction62 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (addChar(charlist,
			Char.chr(Char.ord(String.sub(yytext,2))-Char.ord #"@"));
		    continue())
      end
fun yyAction63 (strm, lastMatch : yymatch) = (yystrm := strm;
      (err(yypos,yypos+2) COMPLAIN "illegal control escape; must be one of \
	  \@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\\]^_" nullErrorBody;
	 continue()))
fun yyAction64 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (let val x = Char.ord(String.sub(yytext,1))*100
	     +Char.ord(String.sub(yytext,2))*10
	     +Char.ord(String.sub(yytext,3))
	     -((Char.ord #"0")*111)
  in (if x>255
      then err (yypos,yypos+4) COMPLAIN "illegal ascii escape" nullErrorBody
      else addChar(charlist, Char.chr x);
      continue())
  end)
      end
fun yyAction65 (strm, lastMatch : yymatch) = (yystrm := strm;
      (err (yypos,yypos+1) COMPLAIN "illegal string escape"
		        nullErrorBody; 
		    continue()))
fun yyAction66 (strm, lastMatch : yymatch) = (yystrm := strm;
      (err (yypos,yypos+1) COMPLAIN "illegal non-printing character in string" nullErrorBody;
                    continue()))
fun yyAction67 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (addString(charlist,yytext); continue())
      end
fun yyAction68 (strm, lastMatch : yymatch) = (yystrm := strm;
      (SourceMap.newline sourceMap yypos; continue()))
fun yyAction69 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction70 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN S; stringstart := yypos; continue()))
fun yyAction71 (strm, lastMatch : yymatch) = (yystrm := strm;
      (err (!stringstart,yypos) COMPLAIN "unclosed string"
		        nullErrorBody; 
		    YYBEGIN INITIAL; Tokens.STRING(makeString charlist,!stringstart,yypos+1)))
fun yyAction72 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist, "`"); continue()))
fun yyAction73 (strm, lastMatch : yymatch) = (yystrm := strm;
      (addString(charlist, "^"); continue()))
fun yyAction74 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN AQ;
                    let val x = makeString charlist
                    in
                    Tokens.OBJL(x,yypos,yypos+(size x))
                    end))
fun yyAction75 (strm, lastMatch : yymatch) = (yystrm := strm;
      ((* a closing quote *)
                    YYBEGIN INITIAL;
                    let val x = makeString charlist
                    in
                    Tokens.ENDQ(x,yypos,yypos+(size x))
                    end))
fun yyAction76 (strm, lastMatch : yymatch) = (yystrm := strm;
      (SourceMap.newline sourceMap yypos; addString(charlist,"\n"); continue()))
fun yyAction77 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm; (addString(charlist,yytext); continue())
      end
fun yyAction78 (strm, lastMatch : yymatch) = (yystrm := strm;
      (SourceMap.newline sourceMap yypos; continue()))
fun yyAction79 (strm, lastMatch : yymatch) = (yystrm := strm; (continue()))
fun yyAction80 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (YYBEGIN Q; 
                    let val hash = HashString.hashString yytext
                    in
                    Tokens.AQID(FastSymbol.rawSymbol(hash,yytext),
				yypos,yypos+(size yytext))
                    end)
      end
fun yyAction81 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (YYBEGIN Q; 
                    let val hash = HashString.hashString yytext
                    in
                    Tokens.AQID(FastSymbol.rawSymbol(hash,yytext),
				yypos,yypos+(size yytext))
                    end)
      end
fun yyAction82 (strm, lastMatch : yymatch) = (yystrm := strm;
      (YYBEGIN INITIAL;
                    brack_stack := ((ref 1)::(!brack_stack));
                    Tokens.LPAREN(yypos,yypos+1)))
fun yyAction83 (strm, lastMatch : yymatch) = let
      val yytext = yymktext(strm)
      in
        yystrm := strm;
        (err (yypos,yypos+1) COMPLAIN
		       ("ml lexer: bad character after antiquote "^yytext)
		       nullErrorBody;
                    Tokens.AQID(FastSymbol.rawSymbol(0w0,""),yypos,yypos))
      end
val yyactTable = Vector.fromList([yyAction0, yyAction1, yyAction2, yyAction3,
  yyAction4, yyAction5, yyAction6, yyAction7, yyAction8, yyAction9, yyAction10,
  yyAction11, yyAction12, yyAction13, yyAction14, yyAction15, yyAction16,
  yyAction17, yyAction18, yyAction19, yyAction20, yyAction21, yyAction22,
  yyAction23, yyAction24, yyAction25, yyAction26, yyAction27, yyAction28,
  yyAction29, yyAction30, yyAction31, yyAction32, yyAction33, yyAction34,
  yyAction35, yyAction36, yyAction37, yyAction38, yyAction39, yyAction40,
  yyAction41, yyAction42, yyAction43, yyAction44, yyAction45, yyAction46,
  yyAction47, yyAction48, yyAction49, yyAction50, yyAction51, yyAction52,
  yyAction53, yyAction54, yyAction55, yyAction56, yyAction57, yyAction58,
  yyAction59, yyAction60, yyAction61, yyAction62, yyAction63, yyAction64,
  yyAction65, yyAction66, yyAction67, yyAction68, yyAction69, yyAction70,
  yyAction71, yyAction72, yyAction73, yyAction74, yyAction75, yyAction76,
  yyAction77, yyAction78, yyAction79, yyAction80, yyAction81, yyAction82,
  yyAction83])
in
  if yyInput.eof(!(yystrm))
    then UserDeclarations.eof(yyarg)
    else (case (!(yyss))
       of A => yygo yyactTable (0, !(yystrm), yyNO_MATCH)
        | F => yygo yyactTable (1, !(yystrm), yyNO_MATCH)
        | L => yygo yyactTable (2, !(yystrm), yyNO_MATCH)
        | Q => yygo yyactTable (3, !(yystrm), yyNO_MATCH)
        | S => yygo yyactTable (4, !(yystrm), yyNO_MATCH)
        | AQ => yygo yyactTable (5, !(yystrm), yyNO_MATCH)
        | LL => yygo yyactTable (6, !(yystrm), yyNO_MATCH)
        | LLC => yygo yyactTable (7, !(yystrm), yyNO_MATCH)
        | LLCQ => yygo yyactTable (8, !(yystrm), yyNO_MATCH)
        | INITIAL => yygo yyactTable (9, !(yystrm), yyNO_MATCH)
      (* end case *))
end
            end
	  in 
            continue() 	  
	    handle IO.Io{cause, ...} => raise cause
          end
        in 
          lex 
        end
    in
    fun makeLexer yyinputN = mk (yyInput.mkStream yyinputN)
    fun makeLexer' ins = mk (yyInput.mkStream ins)
    end

  end
