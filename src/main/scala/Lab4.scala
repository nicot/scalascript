object Lab4 extends jsy.util.JsyApplication {
  import jsy.lab4.ast._
  import jsy.lab4.Parser
  
  /*
   * CSCI 3155: Lab 4
   * Dominic Tonozzi
   * 
   * Partner: Matthias Sainz
   * Collaborators: Jacob Resman
   */

  /* Collections and Higher-Order Functions */
  
  /* Lists */
  
  def compressRec[A](l: List[A]): List[A] = l match {
    case Nil | _ :: Nil => l
    case h1 :: (t1 @ (h2 :: _)) => if (h1 == h2) compressRec(t1) else h1::compressRec(t1)
  }
  
  def compressFold[A](l: List[A]): List[A] = l.foldRight(Nil: List[A]){
    (h, acc) => (h, acc) match { 
      case (h, Nil) => List(h)
      case (h, acc) => println(h,acc); if (acc(0) == h) acc else h::acc
    }
  }
  
  def mapFirst[A](f: A => Option[A])(l: List[A]): List[A] = l match {
    case Nil => Nil
    case h :: t => f(h) match {
      case None => h::mapFirst(f)(t)
      case Some(x) => x::t
    }
  }
  
  /* Search Trees */
  
  sealed abstract class Tree {
    def insert(n: Int): Tree = this match {
      case Empty => Node(Empty, n, Empty)
      case Node(l, d, r) => if (n < d) Node(l insert n, d, r) else Node(l, d, r insert n)
    } 
    
    def foldLeft[A](z: A)(f: (A, Int) => A): A = {
      def loop(acc: A, t: Tree): A = t match {
        case Empty => acc
        case Node(l, d, r) => loop(f(loop(acc,r),d),l)
      }
      loop(z, this)
    }
    
    def pretty: String = {
      def p(acc: String, t: Tree, indent: Int): String = t match {
        case Empty => acc
        case Node(l, d, r) =>
          val spacer = " " * indent
          p("%s%d%n".format(spacer, d) + p(acc, l, indent + 2), r, indent + 2)
      } 
      p("", this, 0)
    }
  }
  case object Empty extends Tree
  case class Node(l: Tree, d: Int, r: Tree) extends Tree
  
  def treeFromList(l: List[Int]): Tree =
    l.foldLeft(Empty: Tree){ (acc, i) => acc insert i }
  
  def sum(t: Tree): Int = t.foldLeft(0){ (acc, d) => acc + d }
  
  def strictlyOrdered(t: Tree): Boolean = {
    val (b, _) = t.foldLeft((true, None: Option[Int])){

      (acc,x) => acc match{
        case (bool,None) => (bool,Some(x))
        case (bool,x1) => ((x1.get > x && bool),Some(x))
      }

    }
    b
  }

  /* Type Inference */
  
  // A helper function to check whether a jsy type has a function type in it.
  // While this is completely given, this function is worth studying to see
  // how library functions are used.
  def hasFunctionTyp(t: Typ): Boolean = t match {
    case TFunction(_, _) => true
    case TObj(fields) if (fields exists { case (_, t) => hasFunctionTyp(t) }) => true
    case _ => false
  }
  
  def typeInfer(env: Map[String,Typ], e: Expr): Typ = {
    // Some shortcuts for convenience
    def typ(e1: Expr) = typeInfer(env, e1)
    def err[T](tgot: Typ, e1: Expr): T = throw StaticTypeError(tgot, e1, e)

    e match {
      case Print(e1) => typ(e1); TUndefined
      case N(_) => TNumber
      case B(_) => TBool
      case Undefined => TUndefined
      case S(_) => TString
      case Var(x) => env(x)
      case ConstDecl(x, e1, e2) => typeInfer(env + (x -> typ(e1)), e2)

      case Unary(Neg, e1) => typ(e1) match {
        case TNumber => TNumber
        case tgot => err(tgot, e1)
      }//end neg

      case Unary(Not, e1) => typ(e1) match{
        case TBool => TBool
        case tgot  => err(tgot,e1)
      }//end not

      case Binary(Plus, e1, e2) => (typ(e1),typ(e2)) match{
        case (TNumber,TNumber)  => TNumber
        case (TString, TString) => TString
        case (tgot,tgot1)       => err(tgot,e1)
      }//end plus

      case Binary(Minus|Times|Div, e1, e2) => (typ(e1),typ(e2)) match{
        case (TNumber,TNumber) => TNumber
        case (TNumber,tgot)    => err(tgot,e2)
        case (tgot,TNumber)    => err(tgot,e1)
      }//end minus times div

      case Binary(Eq|Ne, e1, e2) => typ(e1) match{

        case tgot if hasFunctionTyp(tgot) => err(tgot, e1)
        case _ => typ(e2) match {
          case tgot1 if hasFunctionTyp(tgot1) => err(tgot1, e2)
          case _ => if (typ(e1) == typ(e2)) TBool else err(typ(e2), e2)
        }

      }//

      case Binary(Lt|Le|Gt|Ge, e1, e2) => (typ(e1),typ(e2)) match{
        case (TNumber,TNumber) => TBool
        case (TString,TString) => TBool
        case (tgot,tgot1)      => err(tgot,e1)
      }//end L and G

      case Binary(And|Or,e1,e2) => (typ(e1),typ(e2)) match{
        case(TBool,TBool) => TBool
        case(one,two) => err(one,e1)
      }//end and or

      case Binary(Seq, e1, e2) => typ(e1); typ(e2)
         //must typ e1 to check for possible errors in e1

      case If(e1,e2,e3) => (typ(e1),typ(e2),typ(e3)) match{
        case(TBool,x,y) =>{ if(x==y) x else err(y,e2) }
        case (a,_,_)    => err(a,e1)
      }

      case Function(p, params, tann, e1) => {
        // Bind to env1 an environment that extends env with an appropriate binding if
        // the function is potentially recusive.
        val env1 = (p, tann) match {
          case (Some(f), Some(tret)) =>
            val tprime = TFunction(params, tret)
            env + (f -> tprime)
          case (None, _) => env
          case _ => err(TUndefined, e1)
        }

        //create a new env by going through params and
        val env2 = params.foldLeft(env1){
          case (acc,(x,t)) => acc + (x->t)
        }//end

        // Match on whether the return type is specified.
        tann match {
          case None => TFunction(params, typeInfer(env2, e1))
          case Some(rt) => {
            if (rt == typeInfer(env2, e1))
              TFunction(params, rt)
            else
              TFunction(params, err(rt, e1))
          }
        }

      }//end Function

      case Call(e1, args) => typ(e1) match {

        case TFunction(params, tret) if (params.length == args.length) => {
          (params, args).zipped.foreach {

            case (ty,para) => if(ty._2 != typ(para)) err(typ(para),para) else typ(para)

          };
          tret
        }
        case tgot => err(tgot, e1)
      }
      case Obj(fields) => TObj( fields.map{ case(x,y) => (x,typ(y))} )

      case GetField(e1, f) => typ(e1) match{

        case TObj(field) => field.get(f) match{
          case None => err(typ(e1),e1)
          case Some(x) => x
        }

        case _ => err(typ(e1),e1)

      }

    }
  }

  /* Small-Step Interpreter */
  
  def inequalityVal(bop: Bop, v1: Expr, v2: Expr): Boolean = {
    require(bop == Lt || bop == Le || bop == Gt || bop == Ge)
    ((v1, v2): @unchecked) match {
      case (S(s1), S(s2)) =>
        (bop: @unchecked) match {
          case Lt => s1 < s2
          case Le => s1 <= s2
          case Gt => s1 > s2
          case Ge => s1 >= s2
        }
      case (N(n1), N(n2)) =>
        (bop: @unchecked) match {
          case Lt => n1 < n2
          case Le => n1 <= n2
          case Gt => n1 > n2
          case Ge => n1 >= n2
        }
    }
  }
  
  def substitute(e: Expr, v: Expr, x: String): Expr = {
    require(isValue(v))
    
    def subst(e: Expr): Expr = substitute(e, v, x)
    
    e match {
      case N(_) | B(_) | Undefined | S(_) => e
      case Print(e1) => Print(subst(e1))
      case Unary(uop, e1) => Unary(uop, subst(e1))
      case Binary(bop, e1, e2) => Binary(bop, subst(e1), subst(e2))
      case If(e1, e2, e3) => If(subst(e1), subst(e2), subst(e3))
      case Var(y) => if (x == y) v else e
      case ConstDecl(y, e1, e2) => ConstDecl(y, subst(e1), if (x == y) e2 else subst(e2))
      case fun @ Function(p, params, tann, e1) => {

        if(params.exists((t1:(String,Typ)) => t1._1 ==x) || Some(x) == p){
          fun
        }
        else {
          Function(p, params, tann, subst(e1))
        }

      }
      case Call(e1, args) => Call(subst(e1),args.map(subst))
      case Obj(fields) => Obj(fields.mapValues(v => subst(v)))
      case GetField(e1, f) => { if (x != f) GetField(subst(e1),f) else e

      }
    }
  }
  
  def step(e: Expr): Expr = {
    require(!isValue(e))
    
    def stepIfNotValue(e: Expr): Option[Expr] = if (isValue(e)) None else Some(step(e))
    
    e match {
      /* Base Cases: Do Rules */
      case Print(v1) if isValue(v1) => println(pretty(v1)); Undefined
      case Unary(Neg, N(n1)) => N(- n1)
      case Unary(Not, B(b1)) => B(! b1)
      case Binary(Seq, v1, e2) if isValue(v1) => e2
      case Binary(Plus, S(s1), S(s2)) => S(s1 + s2)
      case Binary(Plus, N(n1), N(n2)) => N(n1 + n2)
      case Binary(bop @ (Lt|Le|Gt|Ge), v1, v2) if isValue(v1) && isValue(v2) => B(inequalityVal(bop, v1, v2))
      case Binary(Eq, v1, v2) if isValue(v1) && isValue(v2) => B(v1 == v2)
      case Binary(Ne, v1, v2) if isValue(v1) && isValue(v2) => B(v1 != v2)
      case Binary(And, B(b1), e2) => if (b1) e2 else B(false)
      case Binary(Or, B(b1), e2) => if (b1) B(true) else e2
      case ConstDecl(x, v1, e2) if isValue(v1) => substitute(e2, v1, x)

      case Binary(Minus, N(n1), N(n2)) => N(n1 - n2)
      case Binary(Times, N(n1), N(n2)) => N(n1 * n2)
      case Binary(Div, N(n1), N(n2)) => N(n1 / n2)


      case Call(v1, args) if isValue(v1) && (args forall isValue) =>
        v1 match {
          case Function(p, params, _, e1) => {
            val e1p = (params, args).zipped.foldRight(e1){
              (x,expression) => x match{
                case ((string,ty),value) => substitute(expression,value,string)
              }
            }

            p match {
              case None => e1p
              case Some(x1) => substitute(e1p,v1,x1)
            }
          }

          case _ => throw new StuckError(e)
        }

      case Call(v1 @ Function(_, _, _, _), args) => {
        val args1 = mapFirst { (a: Expr) => if (!isValue(a)) Some(step(a)) else None }(args)
        Call(v1, args1)
      }
      /*** Fill-in more cases here. ***/



      case Obj(field) => {

        val myList = field.toList

        def helper(arg:(String,Expr)):Option[(String,Expr)] = {
          arg match{
            case (s, e1) => if (!isValue(e1)) Some(s, step(e1)) else None
          }
        }

        Obj(mapFirst(helper)(myList).toMap)

      }//end Obj


      case GetField(Obj(fields), f) => fields.get(f) match {
        case Some(e) => e
        case None => throw new StuckError(e)
      }//end getField

      case GetField(e1, f) => GetField(step(e1), f)
        
      /* Inductive Cases: Search Rules */

      case Call(e1, args) => Call(step(e1), args)
      case Print(e1) => Print(step(e1))
      case Unary(uop, e1) => Unary(uop, step(e1))
      case Binary(bop, v1, e2) if isValue(v1) => Binary(bop, v1, step(e2))
      case Binary(bop, e1, e2) => Binary(bop, step(e1), e2)
      case If(B(true), e2, e3) => e2
      case If(B(false), e2, e3) => e3
      case If(e1, e2, e3) => If(step(e1), e2, e3)
      case ConstDecl(x, e1, e2) => ConstDecl(x, step(e1), e2)
      /*** Fill-in more cases here. ***/
      
      /* Everything else is a stuck error. Should not happen if e is well-typed. */
      case _ => throw StuckError(e)
    }
  }
  /* External Interfaces */
  
  this.debug = true // comment this out or set to false if you don't want print debugging information
  
  def inferType(e: Expr): Typ = {
    if (debug) {
      println("------------------------------------------------------------")
      println("Type checking: %s ...".format(e))
    } 
    val t = typeInfer(Map.empty, e)
    if (debug) {
      println("Type: " + pretty(t))
    }
    t
  }
  
  // Interface to run your small-step interpreter and print out the steps of evaluation if debugging. 
  def iterateStep(e: Expr): Expr = {
    require(closed(e))
    def loop(e: Expr, n: Int): Expr = {
      if (debug) { println("Step %s: %s".format(n, e)) }
      if (isValue(e)) e else loop(step(e), n + 1)
    }
    if (debug) {
      println("------------------------------------------------------------")
      println("Evaluating with step ...")
    }
    val v = loop(e, 0)
    if (debug) {
      println("Value: " + v)
    }
    v
  }

  // Convenience to pass in a jsy expression as a string.
  def iterateStep(s: String): Expr = iterateStep(Parser.parse(s))
  
  // Interface for main
  def processFile(file: java.io.File) {
    if (debug) {
      println("============================================================")
      println("File: " + file.getName)
      println("Parsing ...")
    }
    
    val expr =
      handle(None: Option[Expr]) {Some{
        Parser.parseFile(file)
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
