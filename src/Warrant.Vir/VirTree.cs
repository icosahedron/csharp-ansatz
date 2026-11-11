namespace Warrant.Vir;

/// <summary>Traversal of a unit's nodes, which defines node IDs.</summary>
public static class VirTree
{
    /// <summary>
    /// The unit's nodes in pre-order: the body, then the statement, then the script's tactics. A node's ID is its index
    /// in this sequence. Children are visited in encoding field order.
    /// </summary>
    /// <param name="unit">The unit.</param>
    /// <returns>The nodes, parents before children.</returns>
    public static IReadOnlyList<VirNode> PreOrder(VirUnit unit)
    {
        var nodes = new List<VirNode>();
        if (unit.Body is { } body)
        {
            Visit(body, nodes);
        }
        if (unit.Statement is { } statement)
        {
            Visit(statement, nodes);
        }
        foreach (var tactic in unit.Script ?? VirList<TacticNode>.Empty)
        {
            Visit(tactic, nodes);
        }
        return nodes;
    }

    /// <summary>A node's ID: its index in <see cref="PreOrder"/>, found by reference.</summary>
    /// <param name="unit">The unit.</param>
    /// <param name="node">The node.</param>
    /// <returns>The ID, or null when the node is not among the unit's nodes.</returns>
    public static int? IdOf(VirUnit unit, VirNode node)
    {
        var nodes = PreOrder(unit);
        for (int id = 0; id < nodes.Count; id++)
        {
            if (ReferenceEquals(nodes[id], node))
            {
                return id;
            }
        }
        return null;
    }

    /// <summary>The direct children of a node, in encoding field order.</summary>
    /// <param name="node">The node.</param>
    /// <returns>The children.</returns>
    public static IEnumerable<VirNode> Children(VirNode node)
    {
        switch (node)
        {
            case LitExpr or ParamExpr or LocalExpr or SelfExpr or MemberExpr or DiscardPattern
                or DecimalLitExpr or NullExpr or ThrowExpr or ThrowStmt or NoThrowStmt:
                break;
            case IsNullExpr e:
                yield return e.Operand;
                break;
            case UnwrapExpr e:
                yield return e.Operand;
                break;
            case CoalesceExpr e:
                yield return e.L;
                yield return e.R;
                break;
            case AwaitExpr e:
                yield return e.Operand;
                break;
            case ExternalCallExpr e:
                foreach (var a in e.Args)
                {
                    yield return a;
                }
                break;
            case ModelledCallExpr e:
                foreach (var a in e.Args)
                {
                    yield return a;
                }
                break;
            case EvalStmt s:
                yield return s.Value;
                break;
            case RequiresStmt s:
                yield return s.Condition;
                break;
            case EnsuresStmt s:
                yield return s.Condition;
                break;
            case AssertStmt s:
                yield return s.Condition;
                foreach (var tactic in s.Script)
                {
                    yield return tactic;
                }
                break;
            case UnaryExpr e:
                yield return e.Operand;
                break;
            case BinaryExpr e:
                yield return e.L;
                yield return e.R;
                break;
            case LogicalExpr e:
                yield return e.L;
                yield return e.R;
                break;
            case NotExpr e:
                yield return e.Operand;
                break;
            case CompareExpr e:
                yield return e.L;
                yield return e.R;
                break;
            case ConvertExpr e:
                yield return e.Operand;
                break;
            case CondExpr e:
                yield return e.C;
                yield return e.Then;
                yield return e.Else;
                break;
            case CallExpr e:
                foreach (var a in e.Args)
                {
                    yield return a;
                }
                break;
            case NewExpr e:
                foreach (var a in e.Args)
                {
                    yield return a;
                }
                break;
            case GetExpr e:
                yield return e.Target;
                break;
            case WithExpr e:
                yield return e.Base;
                foreach (var u in e.Updates)
                {
                    yield return u.Value;
                }
                break;
            case SwitchExpr e:
                yield return e.Scrutinee;
                foreach (var arm in e.Arms)
                {
                    yield return arm.Pattern;
                    yield return arm.Value;
                }
                break;
            case ImpliesExpr e:
                yield return e.A;
                yield return e.B;
                break;
            case ForAllExpr e:
                yield return e.Body;
                break;
            case ExistsExpr e:
                yield return e.Body;
                break;
            case DecreasesStmt s:
                yield return s.Measure;
                break;
            case TacticNode t:
                foreach (var nested in Nested(t.Args))
                {
                    yield return nested;
                }
                break;
            case DeclStmt s:
                yield return s.Init;
                break;
            case AssignStmt s:
                yield return s.Value;
                break;
            case IfStmt s:
                yield return s.C;
                yield return s.Then;
                if (s.Else is { } e2)
                {
                    yield return e2;
                }
                break;
            case SwitchStmt s:
                yield return s.Scrutinee;
                foreach (var section in s.Sections)
                {
                    foreach (var label in section.Labels)
                    {
                        yield return label;
                    }
                    foreach (var st in section.Body)
                    {
                        yield return st;
                    }
                }
                break;
            case ReturnStmt s:
                yield return s.Value;
                break;
            case BlockStmt s:
                foreach (var st in s.Stmts)
                {
                    yield return st;
                }
                break;
            case ConstPattern p:
                yield return p.Value;
                break;
            case RelationalPattern p:
                yield return p.Value;
                break;
            case AndPattern p:
                yield return p.L;
                yield return p.R;
                break;
            case OrPattern p:
                yield return p.L;
                yield return p.R;
                break;
            case NotPattern p:
                yield return p.Operand;
                break;
            default:
                throw new ArgumentException($"Unknown VIR node {node.GetType().Name}.", nameof(node));
        }
    }

    /// <summary>The tactics nested in a tactic's arguments, including inside options, in argument order.</summary>
    private static IEnumerable<TacticNode> Nested(IEnumerable<VirTacticArg> args)
    {
        foreach (var arg in args)
        {
            switch (arg)
            {
                case TacticArg a:
                    yield return a.Tactic;
                    break;
                case OptionArg { Value: TacticArg a }:
                    yield return a.Tactic;
                    break;
            }
        }
    }

    private static void Visit(VirNode node, List<VirNode> nodes)
    {
        nodes.Add(node);
        foreach (var child in Children(node))
        {
            Visit(child, nodes);
        }
    }
}
