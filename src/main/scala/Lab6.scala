import jsy.lab6.JsyParser
import scala.util.parsing.combinator.Parsers
import scala.util.parsing.input.CharSequenceReader

object Lab6 extends jsy.util.JsyApplication {
  import jsy.lab6.ast._
  
  /*
   * CSCI 3155: Lab 6
   * Dominic Tonozzi and Matthias Sainz
   * 
   * Collaborators: Jacob Resman
   */

  /*** Regular Expression Parsing ***/

  /* We define a recursive decent parser for regular expressions in
   * RegExprParser.
   * 
   * We derive RegExprParser from Parsers in the Scala library to make
   * use of it's handing of input (Input) and parsing results
   * (ParseResult).
   * 
   * The Parsers trait is actually a general purpose combinator parser
   * library that we will not use.
   * 
   * Grammar
   * 
   *   re ::= union
   *   union ::= intersect {| intersect}
   *   intersect ::= concat {& concat}
   *   concat ::= not {not}
   *   not ::= ~ not | star
   *   star ::= atom {*|+|?}
   *   atom ::= ! | # | c | . | ( re )
   * 
   */
  object RegExprParser extends Parsers {
    type Elem = Char

    /* The following items are the relevant pieces inherited from Parsers
     * 
     * type Input = Reader[Elem]
     * sealed abstract class ParseResult[+T] {
     *   val next: Input
     *   def map[U](f: T => U): ParseResult[U]
     * }
     * case class Success[+T](result: T, next: Input) extends ParseResult[T]
     * case class Failure(next: Input) extends ParseResult[Nothing]
     */
    
    def re(next: Input): ParseResult[RegExpr] = union(next)

    def union(next: Input): ParseResult[RegExpr] = intersect(next) match {
      case Success(r, next) => println("In Union"); {
        def unions(acc: RegExpr, next: Input): ParseResult[RegExpr] =
          if (next.atEnd) Success(acc, next)
          else (next.first, next.rest) match {
            case ('|', next) => intersect(next) match {
              case Success(r, next) => unions(RUnion(acc, r), next)
              case _ => Failure("expected intersect", next)
            }
            case _ => Success(acc, next)
          }
        unions(r, next)
      }
      case _ => Failure("expected intersect", next)
    }

    def intersect(next: Input): ParseResult[RegExpr] = concat(next) match{
      case Success(r,next) => println("In intersect"); {
        def intersections(acc: RegExpr, next:Input): ParseResult[RegExpr] =
          if(next.atEnd) Success(acc,next)
          else (next.first, next.rest) match {
            case('&',next) => concat(next) match{
              case Success(r,next) => intersections(RIntersect(acc,r), next)
              case _ => Failure("expected concat",next)
            }
            case _ => Success(acc,next)
          }
        intersections(r,next)
      }
      case _ => Failure("expected concat", next)
    }

    def concat(next: Input): ParseResult[RegExpr] = not(next) match{
      case Success(r,next) => println("In concat"); {
        def concats(acc: RegExpr, next:Input): ParseResult[RegExpr] =
          if(next.atEnd) Success(acc,next)
          else (next.first, next.rest) match {
            case(_,next) => not(next) match{
              case Success(r,next) => concats(RConcat(acc,r), next)
              case _ => Failure("expected something",next)
            }
            case _ => Success(acc,next)
          }
        concats(r,next)
      }
      case _ => Failure("expected something", next)
    }

    def not(next: Input): ParseResult[RegExpr] = star(next) match{

      case Success(r,next) => println("In not");
        if (next.atEnd) Success(r,next)
        else (next.first, next.rest) match{
          case ('~',next) => star(next) match{
            case Success(r,n) => Success(RNeg(r), next)
            case _ => Failure("diffexp", next)
          }
          case _ => Success(r,next)
        }
      case _ => Failure("Noooo",next)

    }

    def star(next: Input): ParseResult[RegExpr] = atom(next) match{
      case Success(r, next) => println("In Star");
        if(next.atEnd) Success(r,next)
        else (next.first, next.rest) match{
          case ('*', next) => atom(next) match{
            case Success(r, n) => Success(RStar(r),next)
            case _ => Failure("Expected Star", next)
          }
          case ('+', next) => atom(next) match{
            case Success(r, n) => Success(RPlus(r),next)
            case _ => Failure("Expected +", next)
          }
          case ('?', next) =>  atom(next) match{
            case Success(r, n) => Success(ROption(r),next)
            case _ => Failure("Expected Star", next)
          }
          case _ => Success(r, next)
        }
      case _ => Failure("Noo in star",next)
    }

    /* This set is useful to check if a Char is/is not a regular expression
       meta-language character.  Use delimiters.contains(c) for a Char c. */
    val delimiters = Set('|', '&', '~', '*', '+', '?', '!', '#', '.', '(', ')')

    def atom(next: Input): ParseResult[RegExpr] =
      if(next.atEnd) Failure("expected atom", next)
      else (next.first, next.rest) match {
        case ('!', next) => Success(RNoString, next)
        case ('#', next) => Success(REmptyString, next)
        case ('.', next) => Success(RAnyChar, next)
        case ('(', next) => re(next) match {
          case Success(r, next) => (next.first, next.rest) match {
            case (')', next) => Success(r, next)
            case _ => Failure("unmatched (", next)
          }
          case fail => fail
        }
        case (c,next) if(!delimiters.contains(c)) => Success(RSingle(c), next)
        case _ => Failure("expected atom", next)
      }
    /* External Interface */
    
    def parse(next: Input): RegExpr = re(next) match {
      case Success(r, next) if (next.atEnd) => r
      case Success(_, next) => throw new SyntaxError("remaining input", next.pos)
      case Failure(msg, next) => throw new SyntaxError(msg, next.pos)
    }

    def parse(s: String): RegExpr = parse(new CharSequenceReader(s))
  } 
  

  /*** Regular Expression Matching ***/
  
  def retest(re: RegExpr, s: String): Boolean = {
    def stretch(re:RegExpr, h: List[Char], t: List[Char]): (Boolean, List[Char]) = {
      // Runs in approximately O(n^5), but it sometimes works
      // Searches through a given list of chars until it hits a match, and returns true and
      // the unmatched portion of the string. If nothing is found, (False,Nil).
      val sc = {chars:List[Char] => chars.isEmpty:Boolean};
      t match {
        case Nil => (test(re, h, sc), Nil)
        case _ => {
          val (pass, rest) = (test(re, h, sc), t)
          if (pass) (pass, rest) else stretch(re, h:+t.head, t.tail)
        }
      }
    }
    def test(re: RegExpr, chars: List[Char], sc: List[Char] => Boolean): Boolean = {
      (re, chars) match {
        /* Basic Operators */
        case (RNoString, _) => false
        case (REmptyString, _) => sc(chars)
        case (RSingle(c1), chars) => chars.length == 1 &&
          c1 == chars.head
        case (RConcat(re1, re2), _) =>
          if (chars.length == 0) test(re1, Nil, sc) && test(re2, Nil, sc)
          else test(re1, List(chars.head), sc) && test(re2, chars.tail, sc)
        case (RUnion(re1, re2), _) => test(re1, chars, sc) || test(re2, chars, sc)
        case (RStar(re1), _) => sc(chars) || {
          val (pass, rest) = stretch(re1, List(chars.head), chars.tail)
          pass && (if (rest.length > 0) test(re, rest, sc) else true) }

        /* Extended Operators */
        case (RAnyChar, _) => chars.length == 1
        case (RPlus(re1), _) => test(re1, chars, sc) || chars.length > 0 &&
          { val (pass, rest) = stretch(re1, List(chars.head), chars.tail)
            if (rest.length > 0 && pass) test(RStar(re1), rest, sc) else pass }
        case (ROption(re1), _) => sc(chars) || test(re1, chars, sc)

        /***** Extra Credit Cases *****/
        case (RIntersect(re1, re2), _) => test(re1, chars, sc) && test(re2, chars, sc)
        case (RNeg(re1), _) => !test(re1, chars, sc)
      }
    }
    test(re, s.toList, { chars => chars.isEmpty })
  }
    /*
    def test(re: RegExpr, chars: List[Char], sc: List[Char] => Boolean): Boolean = {
      (re, chars) match {
        /* Basic Operators */
        case (RNoString, _) => false
        case (REmptyString, _) => sc(chars)
        case (RSingle(c1), chars) => chars.length == 1 &&
          c1 == chars.head
        case (RConcat(re1, re2), _) => test(re1,chars, { rem_chars => test(re2,rem_chars,sc) })
        case (RUnion(re1, re2), _) => test(re1, chars, sc) || test(re2, chars, sc)
        case (RStar(re1), _) =>
          sc(chars) ||
          test(re1,chars, {remchars => if (remchars.length < chars.length) test(RStar(re1),remchars,sc) else false})

        /* Extended Operators */
        case (RAnyChar, _) => chars.length == 1
        case (RPlus(re1), _) => test(re1, chars, sc) || chars.length > 0 &&
          { val (pass, rest) = stretch(re1, List(chars.head), chars.tail)
          if (rest.length > 0 && pass) test(RStar(re1), rest, sc) else pass }
        case (ROption(re1), _) => sc(chars) || test(re1, chars, sc)
        
        /***** Extra Credit Cases *****/
        case (RIntersect(re1, re2), _) => test(re1, chars, sc) && test(re2, chars, sc)
        case (RNeg(re1), _) => !test(re1, chars, sc)
      }
    }
    println(s);
    println(re);
    test(re, s.toList, { chars => chars.isEmpty })
  }
  */
  
  
  /*** JavaScripty Interpreter ***/

  /* This part is optional and only for fun.
   * 
   * If you want your own complete JavaScripty interpreter, you can copy your
   * Lab 5 interpreter here and extend it for the Lab 6 constructs.
   * 
   * By default, a reference JavaScripty interpreter will run using your
   * regular expression tester.
   */
  object MyInterpreter extends jsy.lab6.Interpreter {
    /* Type checking. */
    def typeInfer(env: Map[String,(Mutability,Typ)], e: Expr): Typ =
      throw new UnsupportedOperationException
    
    /* A small-step transition. */
    def stepre(retest: (RegExpr, String) => Boolean)(e: Expr): DoWith[Mem, Expr] = {
      def step(e: Expr): DoWith[Mem, Expr] = {
        require(!isValue(e), "stepping on a value: %s".format(e))
        throw new UnsupportedOperationException
      }
      step(e)
    }
  }


  /*** External Interfaces ***/

  this.debug = true // comment this out or set to false if you don't want print debugging information
  this.maxSteps = Some(500) // comment this out or set to None to not bound the number of steps.

  var useReferenceRegExprParser = true /* set to true to use the reference parser */
  var useReferenceJsyInterpreter = true /* set to false to use your JavaScripty interpreter */

  this.flagOptions = this.flagOptions ++ List(
    ("ref-reparser", jsy.util.options.SetBool(b => useReferenceRegExprParser = b, Some(b => useReferenceRegExprParser == b)), "using the reference regular expression parser"),
    ("ref-jsyinterp", jsy.util.options.SetBool(b => useReferenceJsyInterpreter = b, Some(b => useReferenceJsyInterpreter == b)), "using the reference JavaScripty interpreter")
  )

  // Select the interpreter to use based on the useReferenceJsyInterpreter flag
  val interpreter: jsy.lab6.Interpreter =
    if (useReferenceJsyInterpreter) jsy.lab6.JsyInterpreter else MyInterpreter
  
  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    } 
    val t = interpreter.typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }
  
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  
  case class TerminationError(e: Expr) extends Exception {
    override def toString = JsyParser.formatErrorMessage(e.pos, "TerminationError", "run out of steps in evaluating " + e)
  }

  def iterateStep(e: Expr): Expr = {
    require(closed(e), "not a closed expression: free variables: %s".format(freeVars(e)) )
    val step: Expr => DoWith[Mem, Expr] = interpreter.stepre(retest)
    def loop(e: Expr, n: Int): DoWith[Mem,Expr] =
      if (Some(n) == maxSteps) throw TerminationError(e)
      else if (isValue(e)) doreturn( e )
      else {
        for {
          m <- doget[Mem]
          _ = if (debug) { println("Step %s:%n  %s%n  %s".format(n, m, e)) }
          ep <- step(e)
          epp <- loop(ep, n + 1)
        } yield
        epp
      }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val (m,v) = loop(e, 0)(memempty)
    if (debug) {
      println("Result:%n  %s%n  %s".format(m,v))
    }
    v
  }
  
  // Select the parser to use based on the useReferenceRegExprParser flag
  def parser: JsyParser =
    if (useReferenceRegExprParser) new JsyParser else new JsyParser(RegExprParser.parse)

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(parser.parse(s))
  
  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      if (useReferenceRegExprParser) println("Parsing with reference RegExpr parser ...")
      else println("Parsing with your RegExpr parser ...")
    }
    
    val expr =
      handle(None: Option[Expr]) {Some{
        parser.parseFile(file)
      }} getOrElse {
        return
      }
    
    handle() {
      val t = inferType(expr)
    }
    
    handle() {
      val v1 = iterateStep(expr)
      println(pretty(v1))
    }
  }
  
}
/*

def multlistDirect(l: List[Int], sc: Int => Int): Int = l match{
  case Nil => 1
  case h :: t => h * multListDirect(t)
}

def multlistTail(l: List[Int], sc: Int => Int): Int = l match{
  case Nil => acc
  case 0 :: _ => 0
  case h :: t => multListTail(t, h * acc)
}

def multlistDelayed(l: List[Int], sc: Int => Int): Int = l match{
  case Nil => sc(1)
  case 0 :: _ => 0
  case h :: t => multlistDelayed(t, { multt => sc(h * multt) })
}


 */