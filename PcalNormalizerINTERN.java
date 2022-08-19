

import java.util.ArrayList;

interface PcalNormalizerInterface {
    void start(Node tree);
}

public class PcalNormalizer implements PcalNormalizerInterface{
    String SpecName;

    public PcalNormalizer()
    {
        SpecName = "Spec";
    }
    
    public void start(Node tree)
    {
    	
        normalize(tree);
    }

    private void normalize(Node tree)
    {
        int numOfChildren = tree.jjtGetNumChildren();
        for(int i=0;i<numOfChildren;i++)
        {
            Node childNode = tree.jjtGetChild(i);
            String nodeName = childNode.toString();
            if(nodeName.equals("algorithm"))
            {
                normalizeAlgorithm(childNode);
            }
            else if(nodeName.equals("model"))
            {
                normalize(childNode);
            }
            else if(nodeName.equals("statement"))
            {
                
            }
        }
    }

    private void normalizeAlgorithm(Node node)
    {
        int numOfChildren = node.jjtGetNumChildren();
        for(int i=0;i<numOfChildren;i++)
        {
            Node childNode = node.jjtGetChild(i);
            String nodeName = childNode.toString();
            if(nodeName.equals("process"))
            {
                normalizeProcess(childNode);
            }
            else if(nodeName.equals("statements"))
            {
            	normalizeStatements(childNode);            	
            }
            else if(nodeName.equals("declarations"))
            {
                normalizeDeclarations(childNode);
            }
            else
            {
                //System.out.println("algorithm level node name:" + nodeName);
            }
        }
    }
    private void normalizeProcess(Node node)
    {
        int numOfChildren = node.jjtGetNumChildren();
        for(int i=0;i<numOfChildren;i++)
        {
            Node childNode = node.jjtGetChild(i);
            String nodeName = childNode.toString();
            if(nodeName.equals("statements"))
            {
                normalizeStatements(childNode);
            }
            else if(nodeName.equals("process"))
            {
                normalizeProcess(childNode);
            }
            else if(nodeName.equals("declarations"))
            {
                normalizeDeclarations(childNode);
            }
        }
    }
    private void normalizeDeclarations(Node node)
    {
        int numOfChildren = node.jjtGetNumChildren();
        for(int j=0;j<numOfChildren;j++)
        {
            Node childNode = node.jjtGetChild(j);
            String nodeName = childNode.toString();
            if(nodeName.equals("functDecl"))
            {
                if(childNode.jjtGetNumChildren() > 2)
                {
                    normalizeStatements(childNode.jjtGetChild(childNode.jjtGetNumChildren()-1));
                }
                else
                {
                    normalizeStatements(childNode.jjtGetChild(1));
                }
            }
        }
    }
	/*
	This function normalises the set of statements that can be in the body of an algorithm, process, branch arm, if, with statement,…
	*/

    private void normalizeStatements(Node node)
    {
        int numOfChildren = node.jjtGetNumChildren();
        /*
	This for statement loops over all the statements in a body.
	*/

	for(int i=0;i<numOfChildren;i++)
        {
            Node childNode = node.jjtGetChild(i);
            String nodeString = getStatementName(childNode);
            
            String firstString = childNode.getTextAt(2);
            if(firstString.equals(":")) //if label exists then name of the statement is at location 3
            	firstString = childNode.getTextAt(3);
            else
            	firstString = childNode.getTextAt(1);
            
	//If the current statement is a branch statement then perform normalisation for a branch
            if(nodeString.equals("branch") && firstString.equals("branch"))
            { 
                boolean hasLabel = checkLabelExistenceForStatementAfterBranch(node, i);
                ArrayList<Node> nodes = null;
                //nodes variable collects the unlabelled statements after the branch for normalisation
		 if(!hasLabel)
                {
                     nodes = getNodes(node, i);
                     if(nodes != null)
                     {
                        numOfChildren -= nodes.size();
                     }
                }
		 //Uncomment the line below to display the tree of the branch statement
		 //childNode.dump(">>");

                normalizeBranch(getInstructionNode(childNode), nodes);
                //normalizeBranchLevel2(getInstructionNode(childNode));
            }
            else if(nodeString.equals("with"))
            {
                Node withNode = null;
                if(childNode.jjtGetNumChildren() > 1)
                {
                    withNode = childNode.jjtGetChild(1).jjtGetChild(0);
                }
                else
                {
                    withNode = childNode.jjtGetChild(0).jjtGetChild(0);
                }
                String operator = withNode.getTextAt(3);
                ArrayList<Node> nodes = null;
                if(operator.equals("="))
                {
                    boolean hasLabel = checkLabelExistenceForStatementAfterBranch(node, i);
                    if(!hasLabel)
                    {
                        nodes = getNodes(node, i);
                        if(nodes != null)
                        {
                            numOfChildren -= nodes.size();
                        }
                    }
                    normalizeWith(withNode, nodes);
                }
                else
                {
                	normalizeWith(withNode, nodes);
                }
            }
            else if(nodeString.equals("loop"))
            {
                if(childNode.jjtGetNumChildren() > 1)
                {
                    normalizeStatements(childNode.jjtGetChild(1).jjtGetChild(0).jjtGetChild(0));
                }
                else
                {
                    normalizeStatements(childNode.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0));
                }
            }
            else if(nodeString.equals("ifelse"))
            {
                Node instNode = getInstructionNode(childNode);
            	if(instNode.jjtGetNumChildren() > 0)
            	{
	                String str = (instNode.jjtGetChild(instNode.jjtGetNumChildren()-1)).toString();
	                
	                if(!str.equals("statements"))
	                {
	                    normalizeIf(getInstructionNode(childNode));
	                }
	
	                boolean hasLabel = checkLabelExistenceForStatementAfterBranch(node, i);

	                ArrayList<Node> nodes = null;
	                if(!hasLabel)
	                {
	                     nodes = getNodes(node, i);
	                     if(nodes != null)
	                     {
	                        numOfChildren -= nodes.size();
	                     }
	                }
	                normalizeBranch(getInstructionNode(childNode), nodes);
	                //normalizeBranchLevel2(getInstructionNode(childNode));
            	}
            }
            else if(nodeString.equals("either"))
            {
                Node n = getInstructionNode(childNode);
                n.jjtChangeName("branch");
                
                normalizeEither(n);
            }
            else if(nodeString.equals("when")|| firstString.equals("when"))
            {                
                Node n = getInstructionNode(childNode);
                n.jjtChangeName("branch");

                
                boolean hasLabel = checkLabelExistenceForStatementAfterBranch(node, i);
                ArrayList<Node> nodes = null;
                if(!hasLabel)
                {
                     nodes = getNodes(node, i);
                     if(nodes != null)
                     {
                        numOfChildren -= nodes.size();
                     }
                }
                if(nodes != null)
                {
                    Node statementsNode = new SimpleNode(pcalTreeConstants.JJTSTATEMENTS);

                    for(int k=0;k<nodes.size();k++)
                    {
                        statementsNode.jjtAddChild((Node)nodes.get(k), statementsNode.jjtGetNumChildren());
                    }
                    n.jjtAddChild(statementsNode,1);
                }
                
            }
            else if(nodeString.equals("foreach"))
            {
                Node instNode = getInstructionNode(childNode);
                normalizeForeach(instNode.jjtGetChild(1));
                normalizeStatements(instNode.jjtGetChild(1));

                //System.out.println();
                //normalizeStatements()
            }
            else
            {
                //System.out.println(">>" + nodeString);
            }
        }
    }
    
    private void normalizeEither(Node node)
    {
    	int numOfBranchArms = node.jjtGetNumChildren();
    	
    	for(int j=0;j<numOfBranchArms;j++)
    	{
    		Node statements = node.jjtGetChild(j);
    		Node branchArm = new SimpleNode(pcalTreeConstants.JJTBRANCHARM);
    		Node expression = new SimpleNode(pcalTreeConstants.JJTEXPRESSION);
    		
    		Node t = new SimpleNode(pcalConstants.TRUE);
    		t.setToken("TRUE");
    		expression.jjtAddChild(t, 0);
    		branchArm.jjtAddChild(expression, 0);
    		branchArm.jjtAddChild(statements, 1);
    		node.jjtAddChild(branchArm, j);
    	}
    }
    
    private void normalizeBranchLevel2(Node node)
    {
        int numOfBranchArms = node.jjtGetNumChildren();
        int j=0;

        Node branchArm = node.jjtGetChild(0);
        String cname = branchArm.toString();

        if(cname.equals("expression"))
        {
        	j = 1;
        }
        Node newBranchNode = new SimpleNode(pcalTreeConstants.JJTBRANCH);      
        
    	Node infixOpNode = new SimpleNode(pcalTreeConstants.JJTINFIXOPERATOR);
    	infixOpNode.setToken("/\\");
    	Node lastCondition = null;
    	
        
        for(;j<numOfBranchArms;j++)
        {
            Node statements = null;
            Node condition = null;
        	branchArm = node.jjtGetChild(j);
            String nodeName = branchArm.toString();
            if(nodeName.equals("branchArm"))
            {
                statements = branchArm.jjtGetChild(1);
                condition = branchArm.jjtGetChild(0);
                lastCondition = negateCondition(condition);
            	infixOpNode.jjtAddChild(negateCondition(condition), infixOpNode.jjtGetNumChildren());
            }
            else if(nodeName.equals("statements"))
            {
        		condition = new SimpleNode(pcalTreeConstants.JJTEXPRESSION);
            	if(infixOpNode.jjtGetNumChildren() < 2)
            	{
            		condition.jjtAddChild(lastCondition, 0);
            	}
            	else
            	{
            		condition.jjtAddChild(infixOpNode, 0);
            	}
                statements = branchArm;
            }
            
            int numOfChildren = statements.jjtGetNumChildren();
            
            ArrayList<Node> listOfSts = new ArrayList<Node>();
            boolean branchFound = false;
            for(int i=0;i<numOfChildren;i++)
            {
                Node childNode = statements.jjtGetChild(i);
                String nodeString = getStatementName(childNode);
                
                String firstString = childNode.getTextAt(2);
                if(firstString.equals(":"))
                	firstString = childNode.getTextAt(3);
                else
                	firstString = childNode.getTextAt(1);
                
                if((nodeString.equals("branch") && firstString.equals("branch")) || (nodeString.equals("ifelse") && firstString.equals("if")))
                {
                	Node combined = combineArms(childNode, condition,  listOfSts);
                	int index1 = newBranchNode.jjtGetNumChildren();
                	int index2 = 0;
                	for(;index2 < combined.jjtGetNumChildren();index1++,index2++)
                	{
                		newBranchNode.jjtAddChild(combined.jjtGetChild(index2), index1);
                	}
                	branchFound = true;
                	break;
                }
                else
                {
                	break;
                }
            }
            
            if(!branchFound && !nodeName.equals("statements"))
            {
            	newBranchNode.jjtAddChild(branchArm, newBranchNode.jjtGetNumChildren());
            }
            else if(!branchFound && nodeName.equals("statements"))
            {
            	branchArm = new SimpleNode(pcalTreeConstants.JJTBRANCHARM);
            	branchArm.jjtAddChild(condition, 0);
            	branchArm.jjtAddChild(statements, 1);
            	newBranchNode.jjtAddChild(branchArm, newBranchNode.jjtGetNumChildren());
            }

        }
        int index1 = 0;
        int index2 = 0;
        for(; index2 < newBranchNode.jjtGetNumChildren();index2++,index1++)
        {
        	node.jjtAddChild(newBranchNode.jjtGetChild(index2), index1);
        }
    }
    
    private Node negateCondition(Node condition)
    {
    	Node prefixOpNode = new SimpleNode(pcalTreeConstants.JJTPREFIXOPERATOR);
    	prefixOpNode.setToken("~");
    	prefixOpNode.jjtAddChild(condition, 0);
    
    	
    	return prefixOpNode;
    }
    
    private Node combineArms(Node node, Node condition1, ArrayList<Node> statements1)
    {
    	node = getInstructionNode(node);
    	int numOfBranchArms = node.jjtGetNumChildren();
        int j=0;

        Node branchArm = node.jjtGetChild(0);
        String cname = branchArm.toString();

        if(cname.equals("expression"))
        {	
        	j = 1;
        }
        
        ArrayList<Node> elseConditionList = new ArrayList<Node>();
        
    	
        for(;j<numOfBranchArms;j++)
        {
            Node branchArmBody = null;
            Node condition = null;
        	branchArm = node.jjtGetChild(j);
            String nodeName = branchArm.toString();
            
            if(nodeName.equals("branchArm"))
            {
                condition = branchArm.jjtGetChild(0);
                branchArmBody = branchArm.jjtGetChild(1);
                

            	Node prefixOpNode = new SimpleNode(pcalTreeConstants.JJTPREFIXOPERATOR);
            	prefixOpNode.setToken("~");
            	prefixOpNode.jjtAddChild(condition, 0);
            	
            	elseConditionList.add(prefixOpNode);
           		
            }
            else if(nodeName.equals("statements"))
            {
                branchArmBody = branchArm;
            }
            
            //Create new condition
            if(condition != null && condition1 != null)
            {
            	Node newConditionNode = null;
            	newConditionNode = new SimpleNode(pcalTreeConstants.JJTEXPRESSION);
            	Node infixOpNode = new SimpleNode(pcalTreeConstants.JJTINFIXOPERATOR);
            	infixOpNode.setToken("/\\");
            	infixOpNode.jjtAddChild(condition1, 0);
            	infixOpNode.jjtAddChild(condition, 1);
            	newConditionNode.jjtAddChild(infixOpNode, 0);   
            	branchArm.jjtAddChild(newConditionNode, 0);
            }
            else if(condition1 == null && condition != null)
            {
            	branchArm.jjtAddChild(condition, 0);
            }

            
            //Create new set of statements
            int numOfChildren = branchArmBody.jjtGetNumChildren();
            Node newstatementsNode = new SimpleNode(pcalTreeConstants.JJTSTATEMENTS);
            for(int i=0;i<statements1.size();i++)
            {
                newstatementsNode.jjtAddChild(statements1.get(i), i);
            }
            for(int i=0;i<numOfChildren;i++)
            {
                Node childNode = branchArmBody.jjtGetChild(i);
                newstatementsNode.jjtAddChild(childNode, newstatementsNode.jjtGetNumChildren());
            }
            if(condition == null && condition1 != null)
            {
                Node elseCondition = new SimpleNode(pcalTreeConstants.JJTEXPRESSION);
            	Node infixOpNode = new SimpleNode(pcalTreeConstants.JJTINFIXOPERATOR);
            	infixOpNode.setToken("/\\");
            	infixOpNode.jjtAddChild(condition1, 0);
            	for(int k=0;k< elseConditionList.size();k++)
            	{
            		infixOpNode.jjtAddChild(elseConditionList.get(k), k+1);
            	}
            	elseCondition.jjtAddChild(infixOpNode, 0);   

                
            	branchArm = new SimpleNode(pcalTreeConstants.JJTBRANCHARM);
            	branchArm.jjtAddChild(elseCondition, 0);
            }
            
            branchArm.jjtAddChild(newstatementsNode, 1);
            node.jjtAddChild(branchArm, j);
        }
        return node;
    }

	/*
	This function performs the normalization process on the branch statement. It takes 
	Node node: the branch node that contains the tree of the branch statement
	ArrayList<Node> nodes: contains the unlabelled statement/statements after the branch statement
	
	The statements in the nodes variable are added to the body of each branch arm.
	Details can be found in the thesis.
	*/
    
    private void normalizeSubBranch(Node node, Node saveSecondInfix, Node statementsInsideSubBranch,boolean flag)
    {
    
    	//if flag variable is false their is only sub-branch statement inside the branch arm
    	
    	// To be added to exp
    	// Argument node is branch arm
    	// Argument saveSecondInfix is condition of sub branch (j <3 )
    	
    	System.out.println("Status of flag " + flag);
    	
    	if(!flag)
    	{
	    	Node saveFirstInfix = node.jjtGetChild(0).jjtGetChild(0); // (i > 78 )
	    	Node statmentsCarrier = node.jjtGetChild(1); //node carrier of second branch arm
	    	
	    	/*
	    	 * 
	    	 * Check if the statements inside the sub branch are more than one
	    	 * 
	    	  begin
						branch
							i < 8 then
								i := 7;
						or 	i > 78 then
								branch
									j <3 then
										i := 3;  <-- Here only one, if these are more than one than all childs must be added
								end branch
						end branch
							    	  
	    	 */
	    	if(statementsInsideSubBranch.jjtGetNumChildren() == 1)
	    	{
	    		statmentsCarrier.jjtAddChild(statementsInsideSubBranch.jjtGetChild(0), 0);
	    	}
	    	else {
	    		for(int i=0;i<statementsInsideSubBranch.jjtGetNumChildren();i++)
	    		{
	    			statmentsCarrier.jjtAddChild(statementsInsideSubBranch.jjtGetChild(i), i);
	    		}
	    	}
	    	
	    	System.out.println("Number of childrens after its added from subbranch: " + statmentsCarrier.jjtGetNumChildren());
	    	
	    	Node exp = node.jjtGetChild(0);
	    	
	    	SimpleNode newInfixOperator = new SimpleNode(0);
	    	newInfixOperator.setName("infixOperator");
	    	newInfixOperator.setToken("/\\");
	    	
	    	// Add both conditions to the node
	    	
	    	exp.jjtAddChild(newInfixOperator, 0);
	    	newInfixOperator.jjtAddChild(saveFirstInfix, 0);
	    	newInfixOperator.jjtAddChild(saveSecondInfix, 1);
	    	
    	}
    	// Else if statements inside branch arm are > 1, i.e branch statement + some other statements.
    	else
    	{
    		Node saveFirstInfix = node.jjtGetChild(0).jjtGetChild(0); // (i > 78 )
	    	Node statmentsCarrier = node.jjtGetChild(1); //node carrier of second branch arm
	    	
	    	/*
	    	 * 
	    	 * Check if the statements inside the sub branch are more than one
	    	 * 
	    	  begin
						branch
							i < 8 then
								i := 7;
						or 	i > 78 then
								branch
									j <3 then
										i := 3;  <-- Here only one, if these are more than one than all childs must be added
								end branch
						end branch
							    	  
	    	 */
	    	int control = statmentsCarrier.jjtGetNumChildren();
	    	int controlLoop = 0;
	    	for(int i=statementsInsideSubBranch.jjtGetNumChildren();;i++)
	    	{
	    		statmentsCarrier.jjtAddChild(statementsInsideSubBranch.jjtGetChild(i), i);
	    		controlLoop++;
	    		if(controlLoop == control)
	    			break;
	    	}
	    	
	    	if(statementsInsideSubBranch.jjtGetNumChildren() == 1)
	    	{
	    		statmentsCarrier.jjtAddChild(statementsInsideSubBranch.jjtGetChild(0), 0);
	    	}
	    	else {
	    		for(int i=0;i<statementsInsideSubBranch.jjtGetNumChildren();i++)
	    		{
	    			statmentsCarrier.jjtAddChild(statementsInsideSubBranch.jjtGetChild(i), i);
	    		}
	    	}
	    	
	    	
	    	Node exp = node.jjtGetChild(0);
	    	
	    	SimpleNode newInfixOperator = new SimpleNode(0);
	    	newInfixOperator.setName("infixOperator");
	    	newInfixOperator.setToken("/\\");
	    	
	    	// Add both conditions to the node
	    	
	    	exp.jjtAddChild(newInfixOperator, 0);
	    	newInfixOperator.jjtAddChild(saveFirstInfix, 0);
	    	newInfixOperator.jjtAddChild(saveSecondInfix, 1);
	    	
	    	
	    	// Code to add additional arm to the main branch
	    	
	    	Node referenceToMainNode = node.jjtGetParent(); // = branch in the tree
	    	
	    	int childrenOfMainBranch = referenceToMainNode.jjtGetNumChildren();
	    	
	    	referenceToMainNode.jjtAddChild(node, childrenOfMainBranch);
	    	
	    	Node newBranchArm = referenceToMainNode.jjtGetChild(1);
	    	
	    	Node prefixOperator = new SimpleNode(0);
	    	prefixOperator.setName("prefixOperator");
	    	prefixOperator.setToken("~");
	    	
	    	Node expInNewBranch = new SimpleNode(0);
	    	expInNewBranch.setName("exp");
	    	expInNewBranch.setToken("()");
	    	
	    	expInNewBranch.jjtAddChild(newBranchArm.jjtGetChild(0).jjtGetChild(1), 0);
	    	prefixOperator.jjtAddChild(expInNewBranch, 0);
	    	
	    	newBranchArm.jjtGetChild(0).jjtGetChild(0).jjtGetChild(1).jjtAddChild(prefixOperator, 1); //Uptil here branch with negated condition is added
	    	
	    	// Code to add additional arm to main branch ends here
	    	
	    	
	    	
	    	System.out.println("Test");
    	}
    }
    
    //This is function being called to normalize sub branch, the function above it is not being used
    //Argument = Branch Arm
    private void normalizeSubBranchN(Node node)
    {
    	Node subBranchReference = node.jjtGetChild(1).jjtGetChild(0).jjtGetChild(0).jjtGetChild(0);
    	int numberOfBranchArmsInSubBranch = subBranchReference.jjtGetNumChildren();
    	Node mainBranch = node.jjtGetParent();
    	int mainBranchChildrens = mainBranch.jjtGetNumChildren();
    	int startFrom = 0;
    	
    	startFrom = mainBranchChildrens-1;
    	
    	// Find the number of statements of branch arm that contains sub-branch
    	boolean flag = false;
    	int numberOfStatementsOfBranchArmContainingSubBranch = node.jjtGetChild(1).jjtGetNumChildren();
    	
    	if(numberOfStatementsOfBranchArmContainingSubBranch > 1)
    		flag = true;
    	
    	// Saving things
    	
    	Node expInsideBranch = node.jjtGetChild(0);
    	Node statementsInsideBranch = node.jjtGetChild(1);
    	
    	for (int i=0;i<numberOfBranchArmsInSubBranch;i++)
    	{
    		Node buildNewExpression = new SimpleNode(pcalTreeConstants.JJTEXPRESSION);
    		Node buildNewInfixOperator = new SimpleNode(pcalTreeConstants.JJTINFIXOPERATOR);
    		buildNewInfixOperator.setToken("/\\");
    		buildNewInfixOperator.jjtAddChild(expInsideBranch.jjtGetChild(0), 0);
    		
    		// Now we have to get reference of current branchArm condition with in the sub branch which we are going to append
    		
    		Node currentSubBranchArmCondition = subBranchReference.jjtGetChild(i).jjtGetChild(0).jjtGetChild(0);
    		
    		// Now append this node to the infix operator
    		
    		buildNewInfixOperator.jjtAddChild(currentSubBranchArmCondition, 1);
    		
    		// Append the infix operator /\ to expression
    		
    		
    		buildNewExpression.jjtAddChild(buildNewInfixOperator, 0);
    		
    		// Create new branch arm to be added to main branch
    		
    		Node newBranchArm = new SimpleNode(pcalTreeConstants.JJTBRANCHARM);
    		
    		// Add the builded expression to new branch arm
    		
    		newBranchArm.jjtAddChild(buildNewExpression, 0);
    		
    		// Add statements node to this branch
    		
    		Node newStatementdsNode = subBranchReference.jjtGetChild(i).jjtGetChild(1);
    		
    		if(flag==true)
    		{
    			for(int j=0;j<numberOfStatementsOfBranchArmContainingSubBranch-1;j++)
    			{
    				newStatementdsNode.jjtAddChild(node.jjtGetChild(1).jjtGetChild(j+1), j+1);
    			}
    		}
    		
    		newBranchArm.jjtAddChild(newStatementdsNode, 1);
    		
    		// At the end add this branch arm to the main branch
    		
    		
    		mainBranch.jjtAddChild(newBranchArm, startFrom);
    		
    		startFrom++;
    	}
    	
    	
    	if(flag==true)
    	{
    		int newChildrensOfMainBranch = mainBranch.jjtGetNumChildren();
   
    		if(newChildrensOfMainBranch == 1)
    		{
    			Node expressionForTheLastBranchArm = new SimpleNode(pcalTreeConstants.JJTEXPRESSION);
    			Node infixOp = mainBranch.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0).jjtGetChild(1);
    			Node normalOP = mainBranch.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0).jjtGetChild(0);
    			
    			
    			Node negatedExpression = new SimpleNode(pcalTreeConstants.JJTPREFIXOPERATOR);
    			negatedExpression.setToken("~");
    			negatedExpression.jjtAddChild(infixOp, 0);
    			
    			Node prefixOperatorMain = new SimpleNode(pcalTreeConstants.JJTINFIXOPERATOR);
    			
    			prefixOperatorMain.jjtAddChild(normalOP, 0);
    			prefixOperatorMain.jjtAddChild(negatedExpression, 1);
    			expressionForTheLastBranchArm.jjtAddChild(prefixOperatorMain,0);
    			
    			
    			
    			Node newBracArm = new SimpleNode(pcalTreeConstants.JJTBRANCHARM);
    			
    			newBracArm.jjtAddChild(expressionForTheLastBranchArm, 0);
    			
    			Node statementsAfterNegatedCondition = new SimpleNode(pcalTreeConstants.JJTSTATEMENTS);
    			
    			for(int j=0;j<numberOfStatementsOfBranchArmContainingSubBranch-1;j++)
    			{
    				statementsAfterNegatedCondition.jjtAddChild(node.jjtGetChild(1).jjtGetChild(j+1), j);
    			}
    			newBracArm.jjtAddChild(statementsAfterNegatedCondition, 1);
    			mainBranch.jjtAddChild(newBracArm, newChildrensOfMainBranch);
    			
    		}
    		
    		//negateCondition();
    	}
    	
    	System.out.println("Num of childrens: " + mainBranch.jjtGetNumChildren());
    }
    
    private void normalizeBranch(Node node, ArrayList<Node> nodes)
    {
        int numOfBranchArms = node.jjtGetNumChildren();
        
        int j=0;
        Node c = node.jjtGetChild(0);
        String cname = c.toString();
        //String cn = node.getTextAt(1);
        if(cname.equals("expression"))
        	j = 1;;
        
//*************************************************************************    

	//Loops over all the branch arms    
        for(;j<numOfBranchArms;j++)
        {
            String nodeName = node.jjtGetChild(j).toString();
            Node branchArmBody = null;
		/*This if else statement finds where the body of the branch arm is. In case of ‘else’, expression 			child will not be there.
		*/
            if(nodeName.equals("branchArm"))
            {
                branchArmBody = node.jjtGetChild(j).jjtGetChild(1);
                
            }
            else if(nodeName.equals("statements"))
            {
                branchArmBody = node.jjtGetChild(j);
            }
            
  
            // I added code from here
            
            //branchArmBody = statements Node
            if(branchArmBody.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0).toString().equals("branch"))
            {
            	System.out.println("Test: "+ branchArmBody.jjtGetParent().toString());
            	normalizeSubBranchN(branchArmBody.jjtGetParent()); //Argument = Reference to main branch arm containing sub branch
            	node.dump(" ");
            	
            }
            
            
            // After this Line I've added the following lines
           
            //To check if branch arm have sub branch
            //branchArmBody = statements Node
            
            /*if(branchArmBody.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0).toString().equals("branch"))
            {
            	//Flag will be true if number of statements inside branch arm are more than one (i.e. sub branch + assignment statments)
            	boolean flag = false;
            	int numberOfStatementsInsideBranchArm = branchArmBody.jjtGetNumChildren(); 
            	
            	System.out.println("Number of statements inside branch arm: " + numberOfStatementsInsideBranchArm);
            	
            	if(numberOfStatementsInsideBranchArm > 1)
            		flag = true;
            	//Node of statments inside sub branch
            	//statementsInsideSubBrnach = main Node statements inside sub branch
            	Node statementsInsideSubBrnach = branchArmBody.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0).jjtGetChild(0).jjtGetChild(1);
            	//Save node which holds the infix condition of sub branch
            	Node infixConditionOfSubBranch = branchArmBody.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0).jjtGetChild(0).jjtGetChild(0).jjtGetChild(0);
            	normalizeSubBranch(branchArmBody.jjtGetParent(),infixConditionOfSubBranch,statementsInsideSubBrnach,flag);
            	System.out.println("nested branch");
            }
            node.dump(" ");*/
            // The lines I added finish here

		/*
		This if statement adds the unlabelled statements to each branch arm.
		*/
        
            if(nodes != null)
            {
                for(int k=0;k<nodes.size();k++)
                {
                	Node n = (Node)nodes.get(k);
                	if(j>0)
                	{
                		Node instN = getInstructionNode(n);
                		String name_instN = instN.toString();
                		if(name_instN.equals("ifelse"))
                		{
                			k = nodes.size();
                		}
                	}
               		branchArmBody.jjtAddChild(n, branchArmBody.jjtGetNumChildren());
                }
            }
		//Recursively calls the normalisation process on the inner statements
            normalizeStatements(branchArmBody);
        }
        
        node.dump(" ");
        
        
    }


    private void normalizeForeach(Node node)
    {
    	Node bodyNode = node;
    	//Adding a blank assignment statement node to AST tree as a markup for adding auxillary assignment statement and if then else statement.
    	Node statementNode = new SimpleNode(pcalTreeConstants.JJTSTATEMENT);
        Node instructionNode = new SimpleNode(pcalTreeConstants.JJTINSTRUCTION);
        Node ifelseNode = new SimpleNode(pcalTreeConstants.JJTIFELSE);
        statementNode.jjtAddChild(instructionNode, 0);
        instructionNode.jjtAddChild(ifelseNode, 0);
        bodyNode.jjtAddChild(statementNode, bodyNode.jjtGetNumChildren());
    	
    }
    /**
     * Adds else part to the if statement with a skip statement
     * @param node
     */
    private void normalizeIf(Node node)
    {
   
        Node statementsNode = new SimpleNode(pcalTreeConstants.JJTSTATEMENTS);
        Node statementNode = new SimpleNode(pcalTreeConstants.JJTSTATEMENT);
        Node instructionNode = new SimpleNode(pcalTreeConstants.JJTINSTRUCTION);
        Node skipNode = new SimpleNode(pcalTreeConstants.JJTSKIP);
        statementsNode.jjtAddChild(statementNode, 0);
        statementNode.jjtAddChild(instructionNode, 0);
        instructionNode.jjtAddChild(skipNode, 0);
        node.jjtAddChild(statementsNode,node.jjtGetNumChildren());
        
    }
    private void normalizeWith(Node node, ArrayList<Node> nodes)
    {
        Node bodyNode = node.jjtGetChild(1);
        if(nodes != null)
        {
            for(int k=0;k<nodes.size();k++)
            {
                bodyNode.jjtAddChild((Node)nodes.get(k), bodyNode.jjtGetNumChildren());
            }
        }
        {//adding a blank assignment statement
            Node statementNode = new SimpleNode(pcalTreeConstants.JJTSTATEMENT);        	         
            Node instructionNode = new SimpleNode(pcalTreeConstants.JJTINSTRUCTION);
            Node assignSingleNode = new SimpleNode(pcalTreeConstants.JJTASSIGNSINGLE);
            statementNode.jjtAddChild(instructionNode, 0);
            instructionNode.jjtAddChild(assignSingleNode, 0);
            bodyNode.jjtAddChild(statementNode, bodyNode.jjtGetNumChildren());
        }
        normalizeStatements(bodyNode);
    }
    private String getStatementName(Node node)
    {
        int num = node.jjtGetNumChildren();
        Node nodeInstruction = null;
        String nodeString = "";
        if(num > 1)
        {
            nodeInstruction = node.jjtGetChild(1).jjtGetChild(0);
        }
        else
        {
            nodeInstruction = node.jjtGetChild(0).jjtGetChild(0);
        }
        nodeString = nodeInstruction.toString();
        return nodeString;
    }
    private Node getInstructionNode(Node node)
    {
        int num = node.jjtGetNumChildren();
        Node nodeInstruction = null;
        if(num > 1)
        {
            nodeInstruction = node.jjtGetChild(1).jjtGetChild(0);
        }
        else
        {
            nodeInstruction = node.jjtGetChild(0).jjtGetChild(0);
        }
        return nodeInstruction;
    }
    private ArrayList<Node> getNodes(Node node, int pos)
    {
        ArrayList<Node> nodesList = new ArrayList<Node>();
        int totalNumChildren = node.jjtGetNumChildren();
        int i=pos+1;

        if(i < totalNumChildren)
        {
            for(;i<totalNumChildren;)
            {
                if(isLoopNode(node.jjtGetChild(i)))
                {
                    break;
                }
                else if(nodeHasLabel(node.jjtGetChild(i)))
                {
                    break;
                }
             
                nodesList.add(node.jjtGetChild(i));
                node.jjtRemoveChild(i);
                totalNumChildren--;
            }
        }
        if(nodesList.size() <= 0)
        {
            nodesList = null;
        }
        return nodesList;
    }
    private boolean isLoopNode(Node node)
    {
        String name = "";
        if(nodeHasLabel(node))
        {
            name = node.jjtGetChild(1).jjtGetChild(0).toString();
        }
        else
        {
            name = node.jjtGetChild(0).jjtGetChild(0).toString();
        }
        if(name.equals("foreach") || name.equals("loop"))
        {
            return true;
        }
        return false;
    }
    private boolean nodeHasLabel(Node node)
    {
        if(node.jjtGetNumChildren() > 1)
        {
            return true;
        }
        return false;
    }
    private boolean checkLabelExistenceForStatementAfterBranch(Node node, int nodeNum)
    {
        boolean hasLabel = true;
        if( nodeNum+1 < node.jjtGetNumChildren())
        {
            Node child = node.jjtGetChild(nodeNum+1);
            if(child != null)
            {
                if(child.jjtGetNumChildren() <= 1)
                {
                    hasLabel = false;
                }
            }
        }
        return hasLabel;
    }
}

