

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
    /*
		This is the main function of normalization process that takes the PlusCal2 program in the form of 
		an AST tree and starts performing the normalization process.
	*/
    public void start(Node tree)
    {
    	//tree.dump("");
        normalize(tree);
    }

    /*
		The normalization process ONLY focuses on the normalization of the statements
		Ideally it should only get the portion of the AST that includes Processes and main algorithm, instead
		it has to search for the algorithm part in the AST.
		*/
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

	/*
		The Algorithm part of the AST contains the statements to be normalized, so this function
		looks for the processes, main process of the algorithm and the declaration part. Declarations
		that might contain the function declarations containing the statements to be normalized.
		*/
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
	/*
		A process can have a declaration section (containing the functions), its own 
		set of statements describing its functionality and the child processes.
		They all have statements to be normalized.
		*/
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
	
	/*
		This function normalizes the set of statements associated with the functions.
		*/
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
		This function starts performing the actual normalization process by identifying
		the specific statements and calling their respective normalization functions.
		It is used to normalize the set of statements associated with the main algorithm,
		processes and functions.
		*/
    private void normalizeStatements(Node node)
    {
        int numOfChildren = node.jjtGetNumChildren();
        for(int i=0;i<numOfChildren;i++)
        {
            Node childNode = node.jjtGetChild(i);
            String nodeString = getStatementName(childNode);
            
            String firstString = childNode.getTextAt(2);
            if(firstString.equals(":"))
            	firstString = childNode.getTextAt(3);
            else
            	firstString = childNode.getTextAt(1);
            
            if(nodeString.equals("branch") && firstString.equals("branch"))
            { 
				/*
					A branch statement is normalized by collecting the unlabeled statements after
					it and inserting them in each branch arm.
					*/
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
				
				//If current branch is not already normalized then it should be done.
                if(!childNode.isNormalized())
					normalizeBranch(getInstructionNode(childNode), nodes);
				/*
					A branch statement is marked normalized after completion of normalization 
					process so that its not normalized again. If there's a branch after
					another branch then the second branch needs to be added to each arm of the 
					first branch. Part of AST representing the AST is not recreated for
					copying in each arm as it would be same for all the arms. Its pointer is
					added.
					*/
				childNode.Normalized();
                //normalizeBranchLevel2(getInstructionNode(childNode));
            }
            else if(nodeString.equals("with"))
            {
                Node withNode = null;
				Node withBody = null;
                if(childNode.jjtGetNumChildren() > 1)	//If the with statement has a label.
                {
                    withNode = childNode.jjtGetChild(1).jjtGetChild(0);
					withBody = childNode.jjtGetChild(1).jjtGetChild(0).jjtGetChild(1);
                }
                else	// If the with statement is not labeled.
                {
                    withNode = childNode.jjtGetChild(0).jjtGetChild(0);
					withBody = childNode.jjtGetChild(0).jjtGetChild(0).jjtGetChild(1);
                }
                String operator = withNode.getTextAt(3);
                ArrayList<Node> nodes = null;
                if(operator.equals("="))
                {
                    int numStatments = withBody.jjtGetNumChildren();
					String statementName = getStatementName(withBody.jjtGetChild(numStatments-1));
					boolean hasLabel = checkLabelExistenceForStatementAfterBranch(node, i);
					//unlabeled statements after current can only be normalized, if the last statement inside the with statement is not another with statement
                    if(!hasLabel && !statementName.equals("with"))
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
				
				//If current branch is not already normalized then it should be done.
                if(!childNode.isNormalized())
					normalizeBranch(getInstructionNode(childNode), nodes);

				childNode.Normalized();

            }
            else if(nodeString.equals("when")|| firstString.equals("when"))
            {                
				/* Normalizes the when statement by 
					-	converting it into a branch statement.
					-	associating all the unlabeled statements after it with the when statement
					-	calls normalization process for the newly created block of statements represented by the variable "statementsNode"
					*/
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
					normalizeStatements(statementsNode);	
                }
                
            }
            else if(nodeString.equals("foreach"))
            {
                Node instNode = getInstructionNode(childNode);
                //normalizeForeach(instNode.jjtGetChild(1));   Adding useles statement for markup Requrires change
                normalizeStatements(instNode.jjtGetChild(1));

            }
			else if(nodeString.equals("atomic"))
			{
                if(childNode.jjtGetNumChildren() > 1)
                {
                    normalizeStatements(childNode.jjtGetChild(1).jjtGetChild(0).jjtGetChild(0));
                }
                else
                {
                    normalizeStatements(childNode.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0));
                }
				normalizeAtomic(childNode);
			}
            else
            {
                //System.out.println(">>" + nodeString);
            }
        }
    }
	
	private void normalizeAtomic(Node node)
	{
		Node child = null;
		if(node.jjtGetNumChildren() == 2)
		{
			child = node.jjtGetChild(1).jjtGetChild(0).jjtGetChild(0);
		}
		else
		{
			child = node.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0);
		}
        //normalizeStatements(child);
		int numChildren = child.jjtGetNumChildren();

		if(numChildren == 1)	//Confirms the we are inside the ___ statement.
		{
	         Node Instruction = child.jjtGetChild(0); //get first statement
	        Node childInstruction = (Instruction.jjtGetNumChildren() == 2 ? Instruction.jjtGetChild(1) : Instruction.jjtGetChild(0));
	        String instructionName = (childInstruction.jjtGetChild(0)).toString();
			
			if(instructionName.equals("branch"))
			{
				checkBranch(Instruction);
			}
		}
	}
	
	/*
		Given a branch statement, this function marks each arm of the branch whether it contains a label or not. If it does then atomic statement must be active for that arm only
		*/
	
	private void checkBranch(Node branch)
	{
		//"branchInstruction" points to the tree for branch statement starting with "branch" label at the start
			Node branchInstruction = branch.jjtGetChild(0).jjtGetChild(0);
			int numChildren = branchInstruction.jjtGetNumChildren();
			
            for(int i=0;i<numChildren;i++)	//loops over all the arms of the branch statement
			{
	    		Node t = new SimpleNode(pcalConstants.TRUE);
	    		t.setToken("TRUE");
//	    		block.jjtAddChild(t, 2);

				Node block = branchInstruction.jjtGetChild(i);	//block points to a branch arm tree
//				normalizeStatements(block);	//must normalize the statements as well!!!!!!!

				if(block.jjtGetNumChildren() == 2)	//If the branch arm is just an else statement then it wont have an "expression" tree, it will only have a "statements" tree.
				{
					block = block.jjtGetChild(1);
				}
				boolean found = findLabelInBlock(block);
				if(!found)
				{
					//System.out.println(">>>label not found");
					block.BlockNotContainsLabel();
					//block.dump(i + ">");
					
				}
			}
		
	}
	/*
		Given a block of statements, this function identifies if the given block contains any label or not.(requires update)
		*/
	
	private boolean findLabelInBlock(Node block)
	{
        for(int j=0;j<block.jjtGetNumChildren();j++)	//loops over all the statements in the block of with except the last one.
		{
			Node statement = block.jjtGetChild(j);
			Node instruction = null;
			if(statement.jjtGetNumChildren() == 2)
			{
				//System.out.println(">>>label found");
				return true;
//				Instruction = statement.jjtGetChild(1).jjtGetChild(0);
			}
		}
		
        for(int j=0;j<block.jjtGetNumChildren();j++)	//loops over all the statements in the block of with except the last one.
		{
			Node statement = block.jjtGetChild(j);
			Node instruction = null;
			if(statement.jjtGetNumChildren() == 2)
			{
				return true;
			}
			else if(statement.jjtGetNumChildren() == 1)
			{
				instruction = statement.jjtGetChild(0).jjtGetChild(0);
			}
			else
			{
				statement.dump("+++");
			}
			String instructionName = instruction.toString();
            if(instructionName.equals("foreach") || instructionName.equals("loop"))// || instructionName.equals("pGoto") || instructionName.equals("pReturn") || instructionName.equals("pBreak"))
			{
				//System.out.println(">>>label will be here ");
				return true;
			}	
			
			if(instructionName.equals("branch") || instructionName.equals("ifelse"))
			{
				checkBranch(statement);
			}
			
		}								
		
		return false;
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
        for(;j<numOfBranchArms;j++)
        {
            String nodeName = node.jjtGetChild(j).toString();
            Node branchArmBody = null;
            if(nodeName.equals("branchArm"))
            {
                branchArmBody = node.jjtGetChild(j).jjtGetChild(1);
            }
            else if(nodeName.equals("statements"))
            {
                branchArmBody = node.jjtGetChild(j);
            }

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
            normalizeStatements(branchArmBody);
        }
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
		//SABINA: remove this blank statement
/*        {//adding a blank assignment statement
            Node statementNode = new SimpleNode(pcalTreeConstants.JJTSTATEMENT);        	         
            Node instructionNode = new SimpleNode(pcalTreeConstants.JJTINSTRUCTION);
            Node assignSingleNode = new SimpleNode(pcalTreeConstants.JJTASSIGNSINGLE);
            statementNode.jjtAddChild(instructionNode, 0);
            instructionNode.jjtAddChild(assignSingleNode, 0);
            bodyNode.jjtAddChild(statementNode, bodyNode.jjtGetNumChildren());
        }*/
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
	/*
		This function returns the all the unlabeled statements from the position 
		specified by the variable "pos" in the current block of statements.
		*/
    private ArrayList<Node> getNodes(Node node, int pos)
    {
        ArrayList<Node> nodesList = new ArrayList<Node>();
        int totalNumChildren = node.jjtGetNumChildren();
        int i=pos+1;

        if(i < totalNumChildren)
        {
            for(;i<totalNumChildren;)
            {
                if(isMustLabelNode(node.jjtGetChild(i)))
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
    private boolean isMustLabelNode(Node node)
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
        if(name.equals("foreach") || name.equals("loop") || name.equals("atomic"))
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
