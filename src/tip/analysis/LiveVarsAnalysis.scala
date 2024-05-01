package tip.analysis

import tip.ast._
import tip.lattices._
import tip.ast.AstNodeData.DeclarationData
import tip.solvers._
import tip.cfg._

import scala.collection.immutable.Set

/**
  * Base class for live variables analysis.
  */
abstract class LiveVarsAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis(false) {

  val lattice: MapLattice[CfgNode, PowersetLattice[ADeclaration]] = new MapLattice(new PowersetLattice())

  val domain: Set[CfgNode] = cfg.nodes

  NoPointers.assertContainsProgram(cfg.prog)
  NoRecords.assertContainsProgram(cfg.prog)

  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element =
    n match {
      case _: CfgFunExitNode => lattice.sublattice.bottom
      case r: CfgStmtNode =>
        r.data match {
          case cond: AExpr => s ++ vars(cond)
          case as: AAssignStmt =>
            as.left match {
              case id: AIdentifier => s - declData(id) ++ vars(as.right)
              case _ => ???
            }
          case varr: AVarStmt => s -- varr.declIds
          case ret: AReturnStmt => s ++ vars(ret.exp)
          case out: AOutputStmt => s ++ vars(out.exp)
          case _ => s
        }
      case _ => s
    }

  private def vars(e: AExpr): Seq[ADeclaration] = {
    e match {
      case ACallFuncExpr(_, args, _) => args.flatMap(vars)
      case id@AIdentifier(_, _) => Seq(declData(id))
      case ABinaryOp(_, left, right, _) => vars(left) ++ vars(right)
      case AUnaryOp(_, subexp, _) => vars(subexp)
      case AAlloc(exp, _) => vars(exp)
      case AVarRef(id, _) => Seq(declData(id))
      case _ => List.empty
    }
  }
}

/**
  * Live variables analysis that uses the simple fixpoint solver.
  */
class LiveVarsAnalysisSimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends LiveVarsAnalysis(cfg)
    with SimpleMapLatticeFixpointSolver[CfgNode]
    with BackwardDependencies

/**
  * Live variables analysis that uses the worklist solver.
  */
class LiveVarsAnalysisWorklistSolver(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData)
    extends LiveVarsAnalysis(cfg)
    with SimpleWorklistFixpointSolver[CfgNode]
    with BackwardDependencies
