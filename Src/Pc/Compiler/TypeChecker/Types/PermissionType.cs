using Microsoft.Pc.TypeChecker.AST;
using Microsoft.Pc.TypeChecker.AST.Declarations;

namespace Microsoft.Pc.TypeChecker.Types
{
    public class PermissionType : PLanguageType
    {
        public PermissionType(Machine machine) : base(TypeKind.Base)
        {
            origin = machine;
            EventSet = machine.Receives;
        }

        public PermissionType(Interface pInterface) : base(TypeKind.Base)
        {
            origin = pInterface;
            EventSet = pInterface.ReceivableEvents;
        }

        public PermissionType(NamedEventSet eventSet) : base(TypeKind.Base)
        {
            origin = eventSet;
            EventSet = eventSet;
        }

        private readonly IPDecl origin;
        public IEventSet EventSet { get; }

        public override string OriginalRepresentation { get; }
        public override string CanonicalRepresentation { get; }

        public override bool IsAssignableFrom(PLanguageType otherType)
        {
            if (otherType is PermissionType permission)
            {
                if (permission.EventSet.IsSupersetOf(this.EventSet))
                {
                    return true;
                }
            }
            return false;
        }

        public override PLanguageType Canonicalize()
        {
            return this;
        }
    }
}