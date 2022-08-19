import java.util.*;


interface PcalTranslatorInterface {
    ExplodedTree start(Node tree, boolean nowarning);
}
/*
	PcalTranslator takes the pluscal algorithm in AST format after it is normalized. 
	The purpose of this class is to prepare the pluscal algorithm for translation in
	TLA+ language. A program in TLA+ contains actions represented by a label from
	the pluscal algorithm. In case if label is not present at a required place, 
	it would create a label at that point.

	The output of this class is another tree (type:ExplodedTree) containing all the 
	actions along with other information in the pluscal algorithm.
*/

public class PcalTranslator implements PcalTranslatorInterface{
    
    private static SymbolTable symTab;
    private Map<String, String> labelList = new HashMap<String,String>();
    private Map<String, String> varList = new LinkedHashMap<String,String>();
    private Map<String, String> globalVarList = new LinkedHashMap<String,String>();
    private String localLabelList = "";
    private String localLabelListForGlobalFunctions = "";
    private String localLabelListForLocalFunctions = "";
    private Map<String, String> pcInitInfoList = new LinkedHashMap<String, String>();
    private int highestLabelNumber = 0;
    private String currentLabelName = "";
    private boolean currentStatementHasLabel = false;
    private boolean isFirstStatementOfBlock = false;
    private boolean isLastStatementOfBlock = false;
    private boolean isBlockOfLoop = false;			//loop statements are labeled at the start, their first statement must be distiguished from the first statement of process,...
    private boolean isBlockOfBranch = false;	
    private boolean isStartOfMethod = false;
    private boolean isWithinBranch = false;
    private boolean isWithinWithBlock = false;
    private boolean branchFinished = false;
    private boolean processFinished = false;	//Marks that a process has finished
    private boolean branchContainedCallReturnGotoLabel = false;
    private boolean wasLastStatementCallReturnGoto = false;
    private boolean stackUpdatedAddLabel = false;
    
    private boolean isGlobal = false;
    private boolean areGlobalVariables = false;
    
    private boolean wasLastStatementProcedureCall = false;
    private boolean isWithinForLoop = false;
    private String currentMethodName = "";
    private String currentMethodType = "";
    private String currentProcessName = "";
    private int currentMethodNOP = 0;
    private Map<String, String> fairListForLabels = new LinkedHashMap<String, String>();
    private String unionOfSetsForFairness = "";
    private String labelAfterLoopForBreakStatement = "";
    private boolean isMainActive = false;
    private Map<String, String> listOfAllProcessIDs = new LinkedHashMap<String, String>();
    private Map<String, setPair> ProcessAndSetNames = new LinkedHashMap<String, setPair>();
    private String lastRangeVaribleName = "";
    private String productOfLastCardinalities = "";
    private ArrayList<String> listOfLabelsAfterLoops = new ArrayList<String>();
    private boolean atomicBlockIsActive = false;
    private boolean haveToAcquireLock = false;		//First block of statements of the atomic block must acquire the lock by setting the variables
    private boolean haveToReleaseLock = false;		//Last block of statements of the atomic block must release the lock by resetting the variables
	private boolean addReleaseLockToBreak = false;		//if the last statemen of atomic is loop then release lock statements must be only added to break statement
    private boolean isStartOfLoopAtomicStatement = false;
    private String labelForStatementAfterLoop = "";
	private String currentLabelOfAtomicBlock = "";
    private String currentLoopLabel = "";
    private boolean wasLastLoopStatement = false;
    private boolean wasForLoopStatement = false;
	private boolean wasSimpleLoopStatement = false;
	private boolean lastActionCompleted = false;	// Remove it! and use a parameter in addupdateinformation function
	private boolean updationAddedbyFor = false;
    private boolean mustGenerateLabel = false; //if atomic statement ended then the next statement after it should have label.
    private boolean labelOfFirstAtomicStatementUsed = false;
    private ArrayList<String> currentAuxVariables = new ArrayList<String>();	//Store the auxilliary variables of with statement only as they are not declared in the state
    private ArrayList<String> currentProcessNames = new ArrayList<String>();
    private ArrayList<String> auxVariablesStack = new ArrayList<String>();
    
    private boolean isExpressionForProperty = false;
    private Map<String, String> listOfQuantVars = new LinkedHashMap<String, String>();//Maintains list of quantification variables used in a property.
	private String conditionStringForProperty = "";
    private boolean isStartOfProperty = false;
    private boolean isAlgorithmLevelProperty = false;
	private String processNameForSelector = "";
	

	private boolean addUpdationAtEnd = false;	//If last statement is an assignment then its updation information must be added as well.
	private boolean dontAddUpdation = false;
    private boolean wasLastBranch = false;		//If last statement was branch then the labels inside branch require pc value.
	
	private String listOfWarnings = "";

//    private boolean isLastStatement; // it is true if the pc value is equal to Done.
    
    //Variables of Foreach loop
    private String auxSetVar_idS_global = "";
    private String setExpression_global = "";
    private String iteratorID_global = "";
    private Node parentNode_global = null;
    private int childNumber_global = 0;
	private class loopInfo{
		public String idSName;
		public String iteratorID;
		public String loopLabel;
		public String nextLabel;
		public Node pNode;
		public int cNumber;
		public boolean releaseLock;
		
	}
    private ArrayList<loopInfo> loopInfos = new ArrayList<loopInfo>();
	
	
	

    //constant used to help handleDefinitionDecls method work properly
    private boolean handDef = false;
    
    //set use to avoid throwing unnecessary warnings
    public static Set<String> knownWords = new HashSet<String>();    
    
    //contains the resulting tree of actions for TLA+ generation
    private ExplodedTree explodedTree = new ExplodedTree(); 
    
    
    /**
     * It is the main function for translating pluscal algorithm to intermediate language.
     * @param tree  It is an AST tree generated by jjtree and normalized by the PcalNormalizer.
     */
    public ExplodedTree start(Node tree, boolean nowarning)
    {
        symTab = new SymbolTable();
        explodedTree.addVariable("depth", "0");
        explodedTree.addVariable("cp", "any");
        globalVarList.put("depth", "0");
        globalVarList.put("cp", "any");
        
		depthFirstTraverse(tree);	//Starts the conversion process from pluscal algorithm to TLA+ actions
        
            String pcInit = "[self \\in ProcSet |-> CASE";
            String varlist = "";
            if(isMainActive)
            {
                String startLabel = localLabelList.substring(0, localLabelList.indexOf(" "));
                localLabelList = "";
                pcInit += "  self = 0 -> \""+startLabel.substring(0, startLabel.indexOf("("))+"\"";
                varlist = "{0}";
            }
            

        if(pcInitInfoList.size() > 0)
        {
            if(isMainActive)
            {
            	varlist += " \\cup ";
            }
            
            for (Iterator iter = listOfAllProcessIDs.entrySet().iterator(); iter.hasNext();)
            {
                Map.Entry entry = (Map.Entry)iter.next();
                String key = (String)entry.getKey();
                String value = (String)entry.getValue();
				if(pcInitInfoList.get(key) != null)
				{
	                if(!isMainActive)
	                {
	                    	pcInit += " self \\in " + value + " -> \"" + pcInitInfoList.get(key) + "\"";
	                    	isMainActive = true;
	                }
	                else
	                {	
						String spaces = "                        ";
	                    pcInit += "\n" + spaces + " []self \\in " + value + " -> \"" + pcInitInfoList.get(key) + "\"";
	                }
				}
            }

            for (Iterator iter = listOfAllProcessIDs.entrySet().iterator(); iter.hasNext();)
            {
                Map.Entry entry = (Map.Entry)iter.next();
                String key = (String)entry.getKey();
                String value = (String)entry.getValue();
				if(pcInitInfoList.get(key) != null)
					varlist += value + " \\cup ";
            }
            varlist = varlist.substring(0, varlist.length()-6);
            explodedTree.addGlobalDefinition("ProcSet", varlist, "", 0);
        }
        else
        {
        	explodedTree.addGlobalDefinition("ProcSet", "{0}", "", 0);

            //explodedTree.addVariable("_pc", "[self \\in 1.._processCount |-> \""+startLabel.substring(0, startLabel.indexOf("("))+"\"]");
        }
            pcInit += "]";
        explodedTree.addVariable("_stack", "[self \\in ProcSet |-> << >>]");
        explodedTree.addVariable("_pc", pcInit);

        explodedTree.copyListOfAllProcessIDs(listOfAllProcessIDs);
        //if(!branchFinished && !wasLastLoopStatement)
        {//to add updation information to the last label generated
        //    addUpdationInformation();
        }
		
		if(!nowarning)
		{
			System.out.print(listOfWarnings);
	        symTab.showWarnings();
		}
        
        //explodedTree.showTree();
        return explodedTree;
    }
    /**
     * It traverses all the nodes of an AST tree.
     * @param node
     */
    private void depthFirstTraverse(Node node)
    {
        String nodeName = node.toString();
        String algoName = "";
        if(nodeName.equals("algorithm"))
        {
            storeCurrentProcessNames(node);		//Records the names of the process at a current level.
        }
        else if(nodeName.compareTo("header") == 0)
        {
            algoName = (node.jjtGetChild(0)).toString();
            String errMsg = symTab.addSymbol(algoName, "algorithm", "");
            if(!errMsg.equals(""))
            {
                handleError(3, node.getLineAndColumnNumber(1) + ":" + errMsg);
            }
            handleHeader(node);
        }
        else if(nodeName.compareTo("declarations") == 0)
        {
        	isGlobal = true;
            areGlobalVariables = true;
            handleDeclarations(node);
            areGlobalVariables = false;
            isGlobal = false;
            return;
        }
        else if(nodeName.compareTo("statements") == 0)
        {
            isMainActive = true;
            explodedTree.setMainActive();
            localLabelList = "";
            
            handleBlock(node, "");
			
			//These two if statements add the updation information in case its not added to the last statement or sets the next pc statement for branch
			if(addUpdationAtEnd && !dontAddUpdation)
				addUpdationInformation(); /* commented because it was adding useless update information at the end of a branch */
			
			if(wasLastBranch)
				explodedTree.setAllNextPC(currentLabelName, "\"Done\"");
			
			

            if(wasLastStatementProcedureCall)
            {
                explodedTree.setCallReturnPCID(currentLabelName, "\"Done\"");
            }
            String actionListName = "_Main";
            explodedTree.addAction(actionListName);
            if(localLabelListForGlobalFunctions.compareTo("") != 0)
            {
                localLabelList += "\\/ " + localLabelListForGlobalFunctions;
            }
            explodedTree.addUpdations(actionListName, "",localLabelList);
            explodedTree.setHasSelf(actionListName);
            if(!wasLastLoopStatement)
				explodedTree.setNextPC(currentLabelName, "\"Done\"");
            explodedTree.setPCID(currentLabelName, createPCID());
	        
			explodedTree.addRangeDefinition("Main", "\t\t0");
			
            return;
        }
        else if(nodeName.compareTo("process") == 0)
        {
            handleProcess(node, null, null, 1);
            return;
        }
        else if(nodeName.compareTo("property") == 0)
        {
            varList.clear();
            handleProperty(node, "Main");
            return;
        }
        else if(nodeName.equals("propertySectionOutsideProcess"))
        {
    		varList.clear();
    		handlePropertySectionOutside(node);
        }
        else if(nodeName.compareTo("instance") == 0)
        {
            handleInstance(node);
            return;
        }
        if(node.jjtGetNumChildren() != 0){
            for(int i=0;i<node.jjtGetNumChildren();i++){
                Node child = node.jjtGetChild(i);         
                depthFirstTraverse(child);                
            }
        }
    }
    /**
     * This function reads the names of the processes at a certain level
     * (global level or process level) and stores them in a global list
     * to allow their access at that level. e.g,

     * variables network = [id \in node |-> <<>>]
     * process node[4]
     * ....
     * 
     * @param node
     */
    private void storeCurrentProcessNames(Node node)
    {
        int i = 1;
        Node pNode = node.jjtGetChild(0);
        String pNode_str = pNode.toString();
        if(pNode_str.equals("process"))
            i = 0;

        for(;i<node.jjtGetNumChildren();i++)
        {
            pNode = node.jjtGetChild(i);
            pNode_str = pNode.toString();
            if(pNode_str.equals("process"))
            {
                currentProcessNames.add(pNode.getTextAt(2));
            }
        }
        symTab.copyCurrentProcessNames(currentProcessNames);
    }
    /**
     * It handles the sub tree representing the header part of the pcal algorithm.
		Header section contains the name of the algorithm, extends section and 
		the constants. The name of the agorithm is extracted before calling this 
		function. This function works on processing the rest of the portion of
		this section.
     * @param node
     */
    private void handleHeader(Node node)
    {
    	String constantText = "\nCONSTANTS any";
    	boolean anyAdded = false;
    	knownWords.add("any");
    	
        if(node.jjtGetNumChildren() > 1)		//If header section contains any extends and constants part
        {
        	for(int i=1;i<node.jjtGetNumChildren();i++)
            {
                Node child = node.jjtGetChild(i);
                String text = child.getTextAt(1);
                
                if(text.compareToIgnoreCase("EXTENDS") == 0)
                {
                    String text1 = child.reproduceText();
                    text1 = text1.substring(text1.indexOf(" "));
                    if(!text1.contains("Sequences"))
                        text1 = text1 + ", Sequences";
                    explodedTree.setHeaderInformation("EXTENDS " + text1);
                }
                else if(text.compareToIgnoreCase("constant") == 0 || text.compareToIgnoreCase("constants") == 0)
                {
                    String text1 = child.reproduceText();
                    text1 = text1.substring(text1.indexOf(" "));
                    knownWords.add(text1.trim());
                    explodedTree.setHeaderInformation("\n" + constantText + "," + text1);
                    handleConstantDecl((text1));
                    anyAdded = true;
                }
            }            
        }
		else	//If it doesn't contains extends and constants portion then it by default adds Sequences module for a 
				//piece of code that is generated automatically with each specification.
		{
        	Node child = node.jjtGetChild(0);
        	
        	String text1 = child.reproduceText();
            
            text1 = " Sequences";
            explodedTree.setHeaderInformation("EXTENDS " + text1);
        }
		
        if(!anyAdded)	//If constant any is not added to the list of constants
        {
            explodedTree.setHeaderInformation("\n" + constantText);
        }
    }
	
	/**
		
		
	**/
    private void handleConstantDecl(String constantDecls)
    {
        String [] consts = constantDecls.split(",");
        int len = consts.length;
        for(int i=0;i<len;i++)
        {
            globalVarList.put(consts[i].replace(" ", ""), "");
            symTab.addSymbol(consts[i].replace(" ", ""), "constant", "");
        }
    }

    private ArrayList<String> generateProcessIDList(Node node, ArrayList<String> processIDList, String processName)
    {
        ArrayList<String> localProcessIDList = new ArrayList<String>();
        if(node.jjtGetNumChildren() > 0)
        {
            Node expNode = node.jjtGetChild(0);
            String firstValue = expNode.reproduceText();
            if(node.jjtGetNumChildren() > 1)
            {
                Node enumNode = node.jjtGetChild(1);
                if(processIDList == null)
                {
                    localProcessIDList.add(processName + "[" + firstValue + "]");
                    for(int i=0;i<enumNode.jjtGetNumChildren();i++)
                    {
                        localProcessIDList.add(processName + "[" + enumNode.jjtGetChild(i).reproduceText() + "]");
                    }
                }
                else
                {
                    for(int j=0;j<processIDList.size();j++)
                    {
                        localProcessIDList.add(processIDList.get(j) + "_" + processName + "[" + firstValue + "]");
                    }
                    for(int j=0;j<processIDList.size();j++)
                    {
                        for(int i=0;i<enumNode.jjtGetNumChildren();i++)
                        {
                            localProcessIDList.add(processIDList.get(j) + "_" + processName + "[" + enumNode.jjtGetChild(i).reproduceText() + "]");
                        }
                    }
                }
            }
            else
            {
                if(processIDList == null)
                {
                    localProcessIDList.add(processName);
                }
                else
                {
                    for(int j=0;j<processIDList.size();j++)
                    {
                        localProcessIDList.add(processIDList.get(j) + "_" + processName);
                    }
                }
            }
        }
        return localProcessIDList;
    }
    private void storeListOfProcessIDs(ArrayList<String> list, String parentName)
    {
        String valueList = "{";
        if(parentName != null)
        {
            parentName = currentProcessName;
            for(int i=0;i<list.size();i++)
            {
                valueList += "\"" + list.get(i) + "\"";
                if(i < list.size()-1)
                {
                    valueList += ", ";
                }
            }
            valueList += "}";
        }
        else
        {
            parentName = currentProcessName;
            for(int i=0;i<list.size();i++)
            {
                valueList += "\"" + list.get(i) + "\"";
                if(i < list.size()-1)
                {
                    valueList += ", ";
                }
            }
            valueList += "}";
        }
        listOfAllProcessIDs.put(parentName, valueList);
    }
    /**
     * It handles the sub tree representing a process.
     * @param node
     */
    private void handleProcess(Node node, ArrayList<String> processIDList, String parentName, int processNum)
    {
       // currentLabelName = "";
        int childNumber = 1;
        String processName = node.getTextAt(2);
        String completeProcessName = "";
        ArrayList<String> localProcessIDList = new ArrayList<String>();
		String pre_localLabelListForLocalFunctions = localLabelListForLocalFunctions;
		
		currentLoopLabel = "";
        
        //if(parentName != null){        
        //	completeProcessName = parentName + "_" + processName;          
        //}else
            completeProcessName = processName;

		// Checks if the name of the process already exists, 
		String errMsg = symTab.addSymbol(completeProcessName, "process", processName);
        if(!errMsg.equals(""))
        {
            handleError(3, node.getLineAndColumnNumber(1) + ":" + errMsg);
        }
		//If the process already exists with the same name within another process for the moment I dont allow process with the same name anywhere in the algorithm
		else if(listOfAllProcessIDs.containsKey(completeProcessName)) 
		{
            handleError(3, node.getLineAndColumnNumber(1) + ": Symbol \""+ completeProcessName+ "\" already exists.");
		}
		/*Updates parent process relationship list*/
		symTab.setProcessParentRelationship(processName, currentProcessName);
        
		currentProcessName = completeProcessName;

		//TO BE CHECKED
        unionOfSetsForFairness = "";
        fairListForLabels.clear();
        
        handleFairness(node.jjtGetChild(childNumber), "process");
        childNumber++;
        
        int numInstances = 0;
        
        if(( (node.jjtGetChild(childNumber).toString()).equals("processHeader")) )
        {
            //localProcessIDList = generateProcessIDList(node.jjtGetChild(childNumber), processIDList, processName);
            //storeListOfProcessIDs(localProcessIDList, parentName);
            //listOfAllProcessIDs.put(completeProcessName, "_" + completeProcessName + "_range");
        	listOfAllProcessIDs.put(completeProcessName, completeProcessName);
        }
		
		
		
        symTab.checkExistenceAddMethod(completeProcessName, "process", "");
        
        setPair parentObj = ProcessAndSetNames.get(parentName);
        setPair obj = null;
/* Code used for processes with headers like: process Server = 2 or process Worker \in Set
        String processSetName = node.jjtGetChild(childNumber).jjtGetChild(0).reproduceText();
        String operatorAfterProcessName = node.jjtGetChild(childNumber).reproduceText();
        operatorAfterProcessName = operatorAfterProcessName.substring(0, 1);
        if(operatorAfterProcessName.equals("="))
        {
            processSetName = "{" + processSetName + "}";
        }
 */
        //************* code for new header process Server[5]
        //String numProcesssInstances = node.jjtGetChild(childNumber).getTextAt(2);
       	String numProcesssInstances = handleExpression(node.jjtGetChild(childNumber).jjtGetChild(0));
        if(parentObj != null)
            obj = new setPair(numProcesssInstances, parentObj.setName);
        else
            obj = new setPair(numProcesssInstances, "");
        ProcessAndSetNames.put(completeProcessName, obj);
//

        childNumber++;
        if(( (node.jjtGetChild(childNumber).toString()).equals("declarations")) )
        {
            handleDeclarations(node.jjtGetChild(childNumber));
            childNumber++;
        }
        symTab.updateDeclarations();

        String data_var, data_val, range_var, range_val;
        String tab = "";
        data_var = data_val = range_var = range_val = "";

        //***
        range_var = completeProcessName;//"_" + completeProcessName + "_range";
        knownWords.add(range_var);
        for(int j=0;j<(range_var.length() + 4);j++)
        {
            tab += " ";
        }
        range_val = tab + "LET " + range_var + "_start == ";
        if(lastRangeVaribleName.equals(""))
        {
            range_val += "1 IN \n";
        }
        else
        {
            range_val += "upperbound(" + lastRangeVaribleName + ") + 1 IN \n";
        }
        tab += " ";
        if(productOfLastCardinalities.equals(""))
        {
            range_val += tab + "LET " + range_var + "_end == ";
            if(lastRangeVaribleName.equals(""))
            {
                range_val += numProcesssInstances + " IN" +
                        "\n" + tab + "    " + range_var + "_start .. " + range_var + "_end";
            }
            else
            {
                range_val += "upperbound(" + lastRangeVaribleName + ") + " + numProcesssInstances + " IN" +
                        "\n" + tab + "    " + range_var + "_start .. " + range_var + "_end";
            }
            productOfLastCardinalities = numProcesssInstances;
        }
        else
        {
            productOfLastCardinalities += " * " + numProcesssInstances;
            range_val += tab + "LET " + range_var + "_end == ";
            range_val += "upperbound(" + lastRangeVaribleName + ") + " + productOfLastCardinalities + " IN" +
                    "\n" + tab + "    " + range_var + "_start .. " + range_var + "_end";
        }

        //*********************
        //explodedTree.addVariable("?"+range_var, range_val);
        //globalVarList.put(range_var, range_val);
        explodedTree.addRangeDefinition(range_var, range_val);

        lastRangeVaribleName = range_var;
        
        localLabelList = "";
        int numChild = node.jjtGetNumChildren();
        String name = "";
        int processChildNum = 0;
        
		// Handles the body of the process after declarations.  It can contain sub-processes, Main part of the process, properties, or property section outside the process
		for(int i=childNumber;i<numChild;i++)
        {
            name = node.jjtGetChild(i).toString();
            if(name.compareTo("process") == 0)
            {
                processChildNum ++;
                handleProcess(node.jjtGetChild(i), localProcessIDList, completeProcessName, processChildNum);
                currentProcessName = completeProcessName;
                symTab.updateDeclarations();
            }
            else if(name.compareTo("statements") == 0)
            {
                currentMethodName = completeProcessName;
                currentMethodType = "process";
                currentMethodNOP = numInstances;
                isStartOfMethod = true;
                
                handleBlock(node.jjtGetChild(i), "");
                
				//These two if statements add the updation information in case its not added to the last statement or sets the next pc statement for branch
				if(addUpdationAtEnd && !dontAddUpdation)
					addUpdationInformation(); 
			
				if(wasLastBranch)
					explodedTree.setAllNextPC(currentLabelName, "\"Done\"");
				
				
				//Following statements need to be checked
				if(wasLastStatementProcedureCall && !wasLastLoopStatement)
                {
                    explodedTree.setCallReturnPCID(currentLabelName, "\"Done\"");
                }
                else if(!currentLoopLabel.equals(""))
                {
                    explodedTree.setCallReturnPCID(currentLabelName, "\"" + currentLoopLabel + "\"");
                }
                
				
				if(branchFinished)
                {
                    explodedTree.setAllNextPC(currentLabelName, "\"Done\"");
                }
                else
                {
                    //addUpdationInformation();
                }                
            }
            else if(name.compareTo("property") == 0)
            {
                varList.clear();
                handleProperty(node.jjtGetChild(i), completeProcessName);
            }
            else if(name.equals("propertySectionOutsideProcess"))
            {
            	Node childPropNode = node.jjtGetChild(i); 
            	for(int j=0;j<childPropNode.jjtGetNumChildren();j++)
            	{
            		varList.clear();
            		handlePropertySectionOutside(childPropNode.jjtGetChild(j));
            	}
            }
        }
        //*****
        symTab.updateDeclarations();
        String parentIDFormula = "";

        data_var = "_" + completeProcessName + "_data";
        if(parentName != null){
            setPair parentSetInfo = ProcessAndSetNames.get(parentName);
            String parentSetInfoString = parentSetInfo.parentSetName;
            if(parentSetInfoString.equals(""))
            {
                parentIDFormula = "( (self - (" + obj.parentSetName + " * " + processNum + ") - FirstElement) \\div " +  obj.setName + " + FirstElement)";
            }
            else
            {
                parentIDFormula = "( (self - (Cardinality(" + listOfAllProcessIDs.get(parentName) + ") * " + processNum + ") - FirstElement) \\div " +  obj.setName + " + FirstElement)";
            }
            String tabs = "            ";
            data_val = "LET FirstElement == lowerbound(" + listOfAllProcessIDs.get(parentName) + ") IN\n" + tabs;
            data_val += data_var + " = [self \\in " + listOfAllProcessIDs.get(completeProcessName) + " |-> [ self |-> self, parentID |-> " + parentIDFormula + ", " + getProcessVariableInitialization(completeProcessName) + "]]";
        }
        else{
            parentIDFormula = "0";
            data_val = "[self \\in " + listOfAllProcessIDs.get(completeProcessName) + " |-> [ self |-> self, parentID |-> " + parentIDFormula + ", " + getProcessVariableInitialization(completeProcessName) + "]]";
        }
        if(parentName != null){
            explodedTree.addVariable("?"+data_var, data_val + "\n");
        }
        else{
            explodedTree.addVariable(data_var, data_val + "\n");
        }
        globalVarList.put(data_var, data_val);
        //*****
        addFairnessInformationToExplodedTree();
        

        if(localLabelListForGlobalFunctions.compareTo("") != 0)
        {
            localLabelList += "\\/ " + localLabelListForGlobalFunctions;
        }
        if(!localLabelListForLocalFunctions.equals(""))
        {
            localLabelList += "\\/ " + localLabelListForLocalFunctions;
        }
		/*
			Adds the list of actions associated with a process
			If a process does not contain any statement then it will not add it instead it will 
			be added to the list processes with no statement to be removed during translation to TLA+
			TOFIX: A process that has not statements, must not have a fair keyword with it.		
			*/
        if(!localLabelList.equals(""))
		{
	        String actionListName = "_" ;
	        actionListName += completeProcessName;
	        explodedTree.addToNextList(actionListName);
	        actionListName += "(self)";
	        explodedTree.addAction(actionListName);
			explodedTree.addUpdations(actionListName, "",localLabelList);
		}
		else
		{
			explodedTree.addNoStatementProcess(completeProcessName);
		}

        
		if(localLabelList.length() > 0)
        {
            pcInitInfoList.put(completeProcessName, localLabelList.substring(0, localLabelList.indexOf("(")));
        }

        if(parentName == null)
        {
            productOfLastCardinalities = "";
        }
        localLabelList = "";
        explodedTree.setPCID(currentLabelName, createPCID());
        symTab.popLastFrame();
        currentMethodName = "";
        currentMethodType = "";
        currentMethodNOP = 0;
        currentProcessName = "";
        if(branchFinished)
        {
            explodedTree.setAllNextPC(currentLabelName, "\"Done\"");
        }
        if(!branchFinished && !wasLastLoopStatement)
        {//to add updation information to the last label generated
        //    addUpdationInformation();
        }
         wasLastLoopStatement = false;
         branchFinished = false;


        explodedTree.setNextPC(currentLabelName, "\"Done\"");
		processFinished = true;		//Marks that a process has finished
		labelForStatementAfterLoop = "";	//Resetting a global variable to avoid invalid generation of label for a new process
		localLabelListForLocalFunctions = pre_localLabelListForLocalFunctions;
		
		//to fix
		wasLastStatementCallReturnGoto = false;
    }

    private String getProcessVariableInitialization(String name)
    {
        Map var_List;
        var_List = symTab.getVarDeclarations(name,"process", 0);

        int listCounter = 0;
        String vars = "Name|->\"" + name + "\"";
        Iterator iter = var_List.entrySet().iterator();
        for (iter = var_List.entrySet().iterator(); iter.hasNext();)
        {
            Map.Entry entry = (Map.Entry)iter.next();
            String key = (String)entry.getKey();
            String value = "";
            value = (String)entry.getValue();
            if(value.compareTo("") == 0)
                value = "\"\"";
            vars += ", " + key + "|->" + value;
            listCounter++;
        }
        return vars;
    }
    private void addFairnessInformationToExplodedTree()
    {
        for (Iterator iter = fairListForLabels.entrySet().iterator(); iter.hasNext();)
        { 
            Map.Entry entry = (Map.Entry)iter.next();
            String key = (String)entry.getKey();
            String value = (String)entry.getValue();
            explodedTree.addToFairList(unionOfSetsForFairness + ":" + key, value);
        }
    }
    /**
     * It handles the sub tree representing a function.
     * @param node
     */
    private void handleFunctionDecls(Node node)
    {
        String type = node.getTextAt(1);
        String name = node.getTextAt(2);
        String errMsg = symTab.addSymbol(name, type, "");
        if(!errMsg.equals(""))
        {
            handleError(3, node.getLineAndColumnNumber(1) + ":" + errMsg);
        }
        
        Node child;
        int numInstances = 0;
        int index = 0;
        child = node.jjtGetChild(index);
        numInstances = handleParameterDecls(child);
        index++;
        symTab.checkExistenceAddMethod(name, type, "");
        
        if(node.jjtGetNumChildren() > 2)
        {
            child = node.jjtGetChild(index);
            handleVarDeclarations(child);
            index++;
        }
        symTab.updateDeclarations();
        
        currentMethodName = name;
        currentMethodType = type;
        currentMethodNOP = numInstances;
        isStartOfMethod = true;
        
        localLabelList = "";
		currentLoopLabel = "";
        
        child = node.jjtGetChild(index);
        handleBlock(child, "");
        symTab.popLastFrame();
        
        if(wasLastStatementProcedureCall)
        {
            explodedTree.setCallReturnPCID(currentLabelName, createStackPCID());
            wasLastStatementProcedureCall = false;
        }
        
        
        if(currentProcessName.compareTo("") == 0)
        {
            if(localLabelListForGlobalFunctions.compareTo("") == 0)
            {
                localLabelListForGlobalFunctions += localLabelList;
            }
            else
            {
                localLabelListForGlobalFunctions += "\\/ " + localLabelList;
            }
        }
        else
        {
            if(localLabelListForLocalFunctions.compareTo("") == 0)
            {
                localLabelListForLocalFunctions += localLabelList;
            }
            else
            {
                localLabelListForLocalFunctions += "\\/ " + localLabelList;
            }
        }
        
        explodedTree.setNextPC(currentLabelName, createStackPCID());
        explodedTree.setPCID(currentLabelName, createPCID());
        if(branchFinished)
        {
            explodedTree.setAllNextPC(currentLabelName, createStackPCID());
        }
        currentMethodName = "";
        currentMethodType = "";
        currentMethodNOP = 0;
        
    }
    /**
     * It handles the parameter declarations for all the methods.
     * @param node
     * @return      It returns number of parameters.
     */
    private int handleParameterDecls(Node node)
    {
        int numChildren = node.jjtGetNumChildren();
        Node child = null;
        String value = "";
        for(int i=0;i<numChildren;i++)
        {
            child = node.jjtGetChild(i);
            if(child.jjtGetNumChildren() == 1)
            {
                value = handleExpression((child.jjtGetChild(0)).jjtGetChild(0));
            }
            else
            {
                value = "{}";
            }
            String newSymbol = generateNewSymbol(child.getTextAt(1));
            String errMsg = symTab.addSymbol(child.getTextAt(1), "parameter", value);
            if(!errMsg.equals(""))
            {
                handleError(3, node.getLineAndColumnNumber(1) + ":" + errMsg);
            }
        }
        return numChildren;
    }
    /**
     * It handles the declaration portion for an algorithm or process.
     * @param node
     */
    private void handleDeclarations(Node node)
    {   
        int numChildren = node.jjtGetNumChildren();
        Node child = null;
        String childName;
        for(int i=0;i<numChildren;i++)
        {
            child = node.jjtGetChild(i);
            childName = child.toString();
            	
            if(childName.compareTo("varDecls") == 0)
            {
                if(isGlobal)
                {
                	areGlobalVariables = true;                	
                }
                handleVarDeclarations(child);
            }
            else if(childName.compareTo("functDecl") == 0)
            {
                handleFunctionDecls(child);
            }
            else if(childName.compareTo("defDecl") == 0)
            {
                handleDefinitionDecls(child);
            }
            else
                System.out.println("Unknown node found.");
        
        }
    }
    private void handleDefinitionDecls(Node node)
    {
        String type = node.getTextAt(1);
        String name = node.getTextAt(2);
        handDef = true;
        symTab.addSymbol(name, type, "");
        Node child;
        int childNum = 0;
        int numInstances = 0;
        String exp = "";
        String parameterString = "";
        
        if(node.jjtGetNumChildren() > 1)
        {//if a definition contains parameters        	
            child = node.jjtGetChild(0);
            numInstances = handleParameterDecls(child);
            parameterString = child.reproduceText();                        
            
            if(!currentProcessName.equals(""))
            {//to add a self parameter by default for definitions                	
                //----------------------------------------------------------------------------
            	knownWords.add(name);
            	String selfPart = "(self,";                
                parameterString = parameterString.substring(1, parameterString.length());
                parameterString = selfPart.concat(parameterString);                
            }
            childNum ++;
        }
        else
        {//if definition do not have a parameter and it belongs to process then it adds a parameter        	
        	if(!currentProcessName.equals("")){            
                parameterString = "(self)";
            }
            else
            {
                parameterString = "";
            }
        }
        symTab.checkExistenceAddMethod(name, type, "");
    
        currentMethodName = name;
        currentMethodType = type;
        currentMethodNOP = numInstances;

        child = node.jjtGetChild(childNum);
        exp = handleExpression(child);          	
        handDef = false;

        if(isGlobal)
        {	
            explodedTree.addGlobalDefinition(name, exp, parameterString, numInstances);
        }
        else
        {
            explodedTree.addAction(numInstances + "_" + name);
            explodedTree.addDefinition(name, exp, parameterString, numInstances);
            explodedTree.setNextPC(currentLabelName, createStackPCID());
            explodedTree.setPCID(currentLabelName, createPCID());
        }
        symTab.popLastFrame();

        currentMethodName = "";
        currentMethodType = "";
        currentMethodNOP = 0;
    }
    /**
     * It handles variables declarations for all the methods.
     * @param node
     */
    private void handleVarDeclarations(Node node)
    {
        int numChildren = node.jjtGetNumChildren();
        Node child = null;
        String value = "";
        
        for(int i=0;i<numChildren;i++)
        {
            child = node.jjtGetChild(i);
            if(child.jjtGetNumChildren() == 1)
            {  
                value = handleExpression((child.jjtGetChild(0)));
            }
            else
            {
                value = "{}";
            }
            String newSymbol = generateNewSymbol(child.toString());
            String errMsg = symTab.addSymbol(child.toString(), "variable", value);
            if(!errMsg.equals(""))
            {
                handleError(3, child.getLineAndColumnNumber(1) + ":" + errMsg);
            }
            
            if(areGlobalVariables)
            {
                explodedTree.addVariable(child.toString(), value);
                globalVarList.put(child.toString(), value);
            }
        }
        if(areGlobalVariables)
        {
            globalVarList.put("_stack", "<< >>");
            explodedTree.addVariable("_pc", "{}");
            globalVarList.put("_pc", "{}");
        }
        areGlobalVariables = false;
    }
    /**
     * It handles the sub tree representing the block of all the methods.
     * @param node
     */
    private void handleBlock(Node node, String calledBy)
    {
        String name = node.toString();
        int numOfStatementsProcessed = 0;
        mustGenerateLabel = false;
		labelForStatementAfterLoop = "";
        if(name.compareTo("statements") == 0)
        {
            int numChildren = node.jjtGetNumChildren();
            Node child = null;
			isLastStatementOfBlock = false;
			checkSyntax(node);
            for(int i=0;i<numChildren;i++)
            {
                if(i == 0 && !isBlockOfLoop && !isBlockOfBranch)
                    isFirstStatementOfBlock = true;
                else
                    isFirstStatementOfBlock = false;
                child = node.jjtGetChild(i);
				if(i+1 == numChildren)
					isLastStatementOfBlock = true;
				if(isLastStatementOfBlock && calledBy.equals("atomic"))// && !isFirstStatementOfBlock)
				{
					haveToReleaseLock = true;
				}
                numOfStatementsProcessed = handleStatement(child, node, i);
                i = i + numOfStatementsProcessed;
            }
			if(calledBy.equals("atomic"))		//To stop the addition of lock release statements as soon as the atomic block ends: Must be redesigned for nested atomic statements
				haveToReleaseLock = false;
        }
        else
        {
            System.out.println("handleBlock:Unknown node found, node name > " + node.reproduceText());
        }
    }
	/*
		*  This function, checkSyntax, checks the syntax of a with statement that allows only few
		*  statements inside its block and in a specific order.
		*  This function must be removed and grammar must be modified in such a way that only valid statements are allowed inside with statement
		*/
	private void checkSyntax(Node node)
	{
		if(isWithinWithBlock)	//Confirms the we are inside the with statement.
		{
            int numChildren = node.jjtGetNumChildren();
//            System.out.println("number of children are: " + numChildren);
            Node child = null;
			boolean withFound = false;
			int withCount = 0;
			
            for(int i=0;i<numChildren-1;i++)	//loops over all the statements in the block of with except the last one.
            {
                child = node.jjtGetChild(i);
                if(child.jjtGetNumChildren() > 1)	//Confirms that the statement does have a label as they are not allowed inside the with statement
                {
                    handleError(5, "");
                }
                else		//Checks if the current statement is valid to be inside with statement
                {
                    Node Instruction = child.jjtGetChild(0);
                    Node childInstruction = child.jjtGetChild(0).jjtGetChild(0);
                    String instructionName = childInstruction.toString();
					//Non of these statements are allowed to be inside with
                    if(instructionName.equals("foreach") || instructionName.equals("loop") || instructionName.equals("pGoto") || instructionName.equals("pReturn") || instructionName.equals("pBreak"))
                    {
	                    handleError(4, "");
					}
					else if(instructionName.equals("with"))	//counts the number of withs
					{
						withFound = true;
						withCount++;
					}
				}
			}
            child = node.jjtGetChild(numChildren-1);
            if(child.jjtGetNumChildren() > 1)   //Confirms that the statement does have a label as they are not allowed inside the with statement
            {
                handleError(5, "");
            }
            else			//Checks if the current statement is valid to be inside with statement
            {
			
            	Node Instruction = child.jjtGetChild(0);
            	Node childInstruction = child.jjtGetChild(0).jjtGetChild(0);
            	String instructionName = childInstruction.toString();
				//Non of these statements are allowed to be inside with
            	if(instructionName.equals("foreach") || instructionName.equals("loop"))
            	{
               	 	handleError(4, "");
				}
				else if((instructionName.equals("ifelse") ||instructionName.equals("branch") ||instructionName.equals("assignSingle") || instructionName.equals("pGoto") || instructionName.equals("pReturn") || instructionName.equals("pBreak")) && withFound )
				{
                	handleError(4, " " + numChildren);
				}
				else if(instructionName.equals("with"))
				{
					withCount++;
				}
			}
			//More than one with statement inside a with are not allowed
			if(withCount > 1)
			{
                handleError(4, "");
			}
			
			//System.out.println(withCount);
		}
	}
    
    /**
     * It handles the sub tree representing a statement.
     * @param node
     */
    private int handleStatement(Node node, Node parentNode, int childNumber)
    {
        int numOfStatementsProcessed = 0;
        String fairnessType = "";
        String labelName = "";
        String colon = "", colonAtPos2, colonAtPos3, colonAtPos4;
        colonAtPos2 = node.getTextAt(2);
        colonAtPos3 = node.getTextAt(3);
        colonAtPos4 = node.getTextAt(4);
        if(colonAtPos2.compareTo(":") == 0)
        {
            labelName = node.getTextAt(1);
            colon = ":";
        }
        else if(colonAtPos3.compareTo(":") == 0)
        {
            fairnessType = node.getTextAt(1);
            if(fairnessType.compareTo("fair") == 0)
            {
                fairnessType = "w";
                labelName = node.getTextAt(2);
                colon = ":";
            }
        }
        else if(colonAtPos4.compareTo(":") == 0)
        {
            fairnessType = node.getTextAt(2);
            if(fairnessType.compareTo("fair") == 0)
            {
                fairnessType = "s";
                labelName = node.getTextAt(3);
                colon = ":";
            }
        }
		        
		String oldLabel = "";
		if(wasLastStatementCallReturnGoto && !branchFinished)
		{
			oldLabel = currentLabelName;
		}

        if((colon.compareTo(":") == 0 || !labelForStatementAfterLoop.equals(""))  && !isStartOfLoopAtomicStatement)//&& !isWithinForLoop
		{
            if(!labelForStatementAfterLoop.equals(""))
            {
                labelName = labelForStatementAfterLoop;
            }
			
            currentLabelName = addLabel(labelName, node.getLineAndColumnNumber(1));
						
            currentStatementHasLabel = true;
            if(isStartOfMethod)
            {
                symTab.setLabelInformation(currentMethodName, currentMethodType, currentMethodNOP, currentLabelName);
                isStartOfMethod = false;
            }
            wasLastStatementCallReturnGoto = false;
            branchContainedCallReturnGotoLabel = false;
            isStartOfLoopAtomicStatement = false;
            labelForStatementAfterLoop = "";
        }
        else if(mustGenerateLabel)
        {
            currentLabelName = generateNewLabel(node.getLineNumber());
            currentStatementHasLabel = true;
            if(isStartOfMethod)
            {
                symTab.setLabelInformation(currentMethodName, currentMethodType, currentMethodNOP, currentLabelName);
                isStartOfMethod = false;
            }
            wasLastStatementCallReturnGoto = false;
            branchContainedCallReturnGotoLabel = false;
            stackUpdatedAddLabel = false;
            isStartOfLoopAtomicStatement = false;
            mustGenerateLabel = false;
        }
        else if((isFirstStatementOfBlock || stackUpdatedAddLabel || wasLastStatementCallReturnGoto || branchContainedCallReturnGotoLabel || branchFinished)  && !haveToAcquireLock && !isStartOfLoopAtomicStatement && !isWithinForLoop)
        {
            String constructName = node.jjtGetChild(0).jjtGetChild(0).toString();
			if(constructName.equals("atomic") || constructName.equals("loop"))
            {
                Node cc = node.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0).jjtGetChild(0);
                labelName = getStatementLabel(cc);

                if(!labelName.equals(""))
                {
                    currentLabelName = addLabel(labelName, cc.getLineAndColumnNumber(1));
                    labelOfFirstAtomicStatementUsed = true;
                }
                else
                {
                    currentLabelName = generateNewLabel(cc.getLineNumber());
                }                
            }
            else
            {
                currentLabelName = generateNewLabel(node.getLineNumber());
            }
            currentStatementHasLabel = true;
            if(isStartOfMethod)
            {
                symTab.setLabelInformation(currentMethodName, currentMethodType, currentMethodNOP, currentLabelName);
                isStartOfMethod = false;
            }
            wasLastStatementCallReturnGoto = false;
            branchContainedCallReturnGotoLabel = false;
            stackUpdatedAddLabel = false;
            isStartOfLoopAtomicStatement = false;
			
        }
        else
		{
            Node c = node.jjtGetChild(0);
            String constructName = "";
            if(c != null)
            {
                constructName = c.getTextAt(1);
                if(constructName.equals("atomic") || constructName.equals("loop"))
                {
                    Node cc = c.jjtGetChild(0).jjtGetChild(0).jjtGetChild(0);
                    labelName = getStatementLabel(cc);
                    if(!labelName.equals(""))
                    {
                        currentLabelName = addLabel(labelName, cc.getLineAndColumnNumber(1));
                        labelOfFirstAtomicStatementUsed = true;
                    }
                    else
                    {
                        currentLabelName = generateNewLabel(cc.getLineNumber());
                    }
                    currentStatementHasLabel = true;

                    if(isStartOfMethod)
                    {
                        symTab.setLabelInformation(currentMethodName, currentMethodType, currentMethodNOP, currentLabelName);
                        isStartOfMethod = false;
                    }
                    wasLastStatementCallReturnGoto = false;
                    branchContainedCallReturnGotoLabel = false;
                    isStartOfLoopAtomicStatement = true;
                }
                else
                {
					//System.out.println("not adding label" + currentLabelName + wasLastStatementCallReturnGoto + " : " + constructName + " : " + haveToAcquireLock);
                    isStartOfLoopAtomicStatement = false;
                    currentStatementHasLabel = false;
                }
            }
            else
            {
				System.out.println("Im at line 1232 :  c is null");
                isStartOfLoopAtomicStatement = false;
                currentStatementHasLabel = false;
            }
        }
		
		if(!oldLabel.equals(""))
		{
            explodedTree.updateStatement(oldLabel, "__stack", "\"" + currentLabelName + "\"");
			oldLabel = "";
		}
		
        
        if(node.jjtGetNumChildren() == 1)
        {
            numOfStatementsProcessed = handleInstruction(node.jjtGetChild(0), parentNode, childNumber);
        }
        else
        {
            handleFairness(node.jjtGetChild(0), "statement");
            numOfStatementsProcessed = handleInstruction(node.jjtGetChild(1), parentNode, childNumber);
        }
		
        return numOfStatementsProcessed;
    }

    private String getStatementLabel(Node node)
    {
        String fairnessType = "";
        String labelName = "";
        String colon = "", colonAtPos2, colonAtPos3, colonAtPos4;
        colonAtPos2 = node.getTextAt(2);
        colonAtPos3 = node.getTextAt(3);
        colonAtPos4 = node.getTextAt(4);
        if(colonAtPos2.compareTo(":") == 0)
        {
            labelName = node.getTextAt(1);
            colon = ":";
        }
        else if(colonAtPos3.compareTo(":") == 0)
        {
            fairnessType = node.getTextAt(1);
            if(fairnessType.compareTo("fair") == 0)
            {
                fairnessType = "w";
                labelName = node.getTextAt(2);
                colon = ":";
            }
        }
        else if(colonAtPos4.compareTo(":") == 0)
        {
            fairnessType = node.getTextAt(2);
            if(fairnessType.compareTo("fair") == 0)
            {
                fairnessType = "s";
                labelName = node.getTextAt(3);
                colon = ":";
            }
        }
        String nodeName = node.jjtGetChild(0).toString();
        String statementName = "";
        if(nodeName.equals("fairness"))
        {
            statementName = node.jjtGetChild(1).jjtGetChild(0).toString();
        }
        else
        {
            statementName = node.jjtGetChild(0).jjtGetChild(0).toString();
        }
        if(statementName.equals("loop"))
        {
            labelName = "";
        }
        return labelName;
    }
    /**
     * It handles the fairness node and collects the information regarding the
     * label. 
     * @param node
     * @param name  It represents a process/thread/statement for which fairness
     * is required.
     */
    private void handleFairness(Node node, String name)
    {
        String text1 = node.getTextAt(1);
        String fairnessType = "";
        if(text1.compareToIgnoreCase("strong") == 0 || text1.compareToIgnoreCase("strongly") == 0)
        {
            fairnessType = "strong";
        }
        else if(text1.compareToIgnoreCase("fair") == 0)
        {
            fairnessType = "weak";
        }
        if(fairnessType.compareToIgnoreCase("") != 0)
        {
            if(name.compareTo("process") == 0)
            {
                explodedTree.addToFairList("_"+currentProcessName, fairnessType);
            }
            else if(name.compareTo("thread") == 0)
            {
                explodedTree.addToFairList("_"+currentProcessName+"_"+currentMethodName, fairnessType);
            }
            else
            {
                if(currentProcessName.compareTo("") == 0 && currentMethodName.compareTo("") == 0)
                {//label belongs to main algorithm
                    explodedTree.addToFairList(":"+currentLabelName, fairnessType);
                }
                else if(currentProcessName.compareTo("") == 0 && currentMethodType.compareTo("function") == 0)
                {//label belongs to global function
                    explodedTree.addToFairList(currentLabelName+":", fairnessType);
                }
                else if(currentProcessName.compareTo("") != 0)
                {
                    if(currentMethodType.compareTo("process") == 0)
                    {
                        explodedTree.addToFairList("_"+currentProcessName+":"+currentLabelName, fairnessType);
                    }
                    else if(currentMethodType.compareTo("thread") == 0)
                    {
                        explodedTree.addToFairList("_"+currentProcessName+"_"+currentMethodName+":"+currentLabelName, fairnessType);
                    }
                    else if(currentMethodType.compareTo("function") == 0)
                    {
                        unionOfSetsForFairness += "_" + currentProcessName + "_IDSet";
                        fairListForLabels.put(currentLabelName, fairnessType);
                    }
                }
            
            }
        }
    }
    /**
     * It handles the sub tree representing an instruction.
     * @param node
     */
    private int handleInstruction(Node node, Node parentNode, int childNumber)
    {
        Node child = node.jjtGetChild(0);
        String instructionName = child.toString();
        int numOfStatementsProcessed = 0;
		
        if(instructionName.compareTo("assignSingle") == 0)
        {
            int numChildren = node.jjtGetNumChildren();
            for(int i=0;i<numChildren;i++)
            {
                child = node.jjtGetChild(i);
                handleAssignment(child);
            }
        }
        else if(instructionName.compareTo("run") == 0)
        {
            handleRun(child);
        }
        else if(instructionName.compareTo("skip") == 0)
        {
            ;
        }
        else if(instructionName.compareTo("pReturn") == 0)
        {
            handleReturn(child);
        }
        else if(instructionName.compareTo("procedureCall") == 0)
        {
			wasLastLoopStatement = false;
            handleProcedureDefinitionCall(child);
        }
        else if(instructionName.compareTo("loop") == 0)
        {
            String firstLabelAfterLoop = getLabelAfterLoop(parentNode, childNumber);
			if(firstLabelAfterLoop.equals("Done") && !currentMethodName.equals("")  && currentMethodType.equals("procedure"))
			{
				firstLabelAfterLoop = createStackPCID();
			}
			boolean pre_haveToReleaseLock = haveToReleaseLock;
			boolean pre_addReleaseLockToBreak = addReleaseLockToBreak;
			if(haveToReleaseLock)
			{
//				System.out.println("loop statement found and have to release lock enabled : " + currentLabelName);
				haveToReleaseLock = false;
				//addReleaseLockToBreak = true;
				addReleaseLockToBreak = (isLastStatementOfBlock) ? true : false;
	            handleLoop(child, firstLabelAfterLoop);
				haveToReleaseLock = true;
			}
			else
			{
				if(addReleaseLockToBreak)
				{
					addReleaseLockToBreak = false;
		            handleLoop(child, firstLabelAfterLoop);
					addReleaseLockToBreak = false;
				}
				else
		            handleLoop(child, firstLabelAfterLoop);
					
			}
			haveToReleaseLock = pre_haveToReleaseLock;
			addReleaseLockToBreak = pre_addReleaseLockToBreak;
        }
        else if(instructionName.compareTo("pGoto") == 0)
        {
            handleGoto(child);
        }
        else if(instructionName.equals("branch"))
        {
            handleBranch(child, false);
        }
        else if(instructionName.equals("ifelse"))
        {
            handleBranch(child, true);
        }
        else if(instructionName.compareTo("print") == 0)
        {
            handlePrint(child);
        }
        else if(instructionName.compareTo("pBreak") == 0)
        {
            //to be done
            if(isWithinForLoop || !labelAfterLoopForBreakStatement.equals(""))
            {
                handleBreak(child);
                wasLastStatementCallReturnGoto = true;
            }
        }
        else if(instructionName.compareTo("foreach") == 0)
        {
           if(!currentStatementHasLabel)
           {
                currentLabelName = generateNewLabel(child.getLineNumber());
                currentStatementHasLabel = true;
           }
           numOfStatementsProcessed = handleForLoop(child, parentNode, childNumber);
		   
/*		   System.out.println("Printing..........");
			   for (int i =0 ; i< loopInfos.size();i++) 
		   {
					/*public String idSName;
					public String iteratorID;
					public String loopLabel;
					public String nextLabel;
					public Node pNode;
					public int cNumber;*/
				/*	loopInfo l = loopInfos.get(i);
		            System.out.println(l.idSName);
		        }*/
		   
        }
        else if(instructionName.compareTo("with") == 0)
        {
           numOfStatementsProcessed = handleWith(child, parentNode, childNumber);           
        }
        else if(instructionName.compareTo("atomic") == 0)
        {
            handleAtomic(child);
        }
        else
        {
            System.out.println("Unknown instruction : " + instructionName);
        }
		 
		//SABINA: These ifelse require cleanup
        //These ifelse statements check for the last statement; if the last statement of the algorithm is assignment, skip, with, atomic, branch, ifelse, or loop then an updation statement must be added or pc value must be set. 
		if(instructionName.equals("assignSingle") ||  instructionName.equals("skip"))
		{
			addUpdationAtEnd = true;
			dontAddUpdation = false;
		}
		else if(instructionName.equals("loop") || instructionName.equals("with") || instructionName.equals("atomic") || instructionName.equals("procedureCall") || instructionName.equals("print"))
		{
			addUpdationAtEnd = true;
		}
		else
			addUpdationAtEnd = false;
		
		if(instructionName.equals("branch") ||instructionName.equals("ifelse"))
			wasLastBranch = true;
		else
			wasLastBranch = false;
		
		//Resetting global variables
		if(!instructionName.equals("loop"))
		{
			wasSimpleLoopStatement = false;
		}
		else if(!instructionName.equals("foreach"))
		{
			wasForLoopStatement = false;
		}
		
		if(instructionName.equals("with") || instructionName.equals("assignSingle") ||  instructionName.equals("skip") || instructionName.equals("branch") || 
			instructionName.equals("ifelse")|| instructionName.equals("atomic") || instructionName.equals("pBreak") || instructionName.equals("pGoto"))
		{
			wasLastLoopStatement = false;
			wasForLoopStatement = false;
		}
		
				
		if(instructionName.equals("assignSingle") ||  instructionName.equals("skip") || instructionName.equals("branch") || 
			instructionName.equals("ifelse"))
		{
			mustGenerateLabel = false;
		}
        
        return numOfStatementsProcessed;
    }
    private void handleBreak(Node node)
    {
        String lhs;
        lhs = createPCID();

        if(isWithinBranch && !isWithinForLoop)
        {
            explodedTree.addUpdations(currentLabelName, "_pc", generateNextPCRHS(labelAfterLoopForBreakStatement));
            wasLastStatementCallReturnGoto = true;
			//System.out.println("Its break directly inside branch................." + currentLabelName + isWithinForLoop);
        }
		else if(isWithinForLoop)
		{ 
			if(loopInfos.size()  > 0)
			{
		  		loopInfo lInfo = loopInfos.remove(loopInfos.size()-1);
                addAssignedVariableToVarList(lInfo.idSName);
                addAssignedVariableToVarList(lInfo.iteratorID);
				explodedTree.addAuxStatement(currentLabelName, "_" + lInfo.idSName, "{}");
		        explodedTree.addAuxStatement(currentLabelName, checkVariableAssignment(lInfo.iteratorID), "{}");
				
				String nextlabel = "";
				int numOfStatementsProcessed = 0;
				//The following 2 statements only find out the label's name after the for loop they do not make any changes to the exploded tree.
	            numOfStatementsProcessed = handleRestOfStatements(lInfo.pNode, lInfo.cNumber, true);

		  		if(loopInfos.size() > 0)
				{
					loopInfo lastLoopInfo = loopInfos.get(loopInfos.size()-1);
					nextlabel = lastLoopInfo.nextLabel;
				}
				if(!(lInfo.nextLabel).equals(nextlabel))
				{
					handleRestOfStatements(lInfo.pNode, lInfo.cNumber, false);
	                explodedTree.addUpdations(currentLabelName, "_pc", generateNextPCRHS(lInfo.nextLabel));
//	                if(!isWithinBranch)
//						addUpdationInformation();
				}
				else
				{
					if(loopInfos.size() > 0)
					{	
						if(numOfStatementsProcessed > 0)
							handleRestOfStatements(lInfo.pNode, lInfo.cNumber, false);
						addAuxStatementsForForeach(1);	
					}
					else// Adds the else part for the second ifthenelse of the for loop statement
					{
			            numOfStatementsProcessed = handleRestOfStatements(lInfo.pNode, lInfo.cNumber, false);
           
			            explodedTree.addUpdations(currentLabelName, "_pc", generateNextPCRHS(lInfo.nextLabel));
//		                if(!isWithinBranch)
//							addUpdationInformation();
					}
				}
					
				loopInfos.add(lInfo);
				
				
				
//		            rhs = "[_pc EXCEPT ![self] = \"" + lInfo.nextLabel + "\"]";
//		            explodedTree.addUpdations(currentLabelName, "_pc", rhs);
		            wasLastStatementCallReturnGoto = true;
					mustGenerateLabel = true;
			}
//			System.out.println("Im here.................");
			
		}
        else
        {
            explodedTree.setNextPC(currentLabelName, generateNextPCRHS(labelAfterLoopForBreakStatement));
            explodedTree.setPCID(currentLabelName, createPCID());
        }
        //isWithinBranch = false;
		
		if(addReleaseLockToBreak)
		{
            varList.put("cp", "IF depth - 1 = 0 THEN any ELSE self");
            varList.put("depth", "depth - 1");
		}
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

    /**
     * It handles the subtree representing the print statement.
	 * It adds the print statement as a statement in the etree.
		LHS contains "print"  that identifies the is should be treated as print statement during TLA generation stage.
		RHS contains the exact statement for TLA code
     * @param node
     */
    private void handlePrint(Node node)
    {
        Node instructionNode = getInstructionNode(node);
//		System.out.println(instructionNode.jjtGetNumChildren());
        //Node expressionNode = instructionNode.jjtGetChild(0);
        String expression = handleExpression(instructionNode);
        explodedTree.addStatement(currentLabelName, "print", "PrintT("+expression+")");
		//System.out.println(expression);
        //explodedTree.addUpdations(currentLabelName, "PrintT("+expression+")", "");
        //varList.put("PrintT("+expression+")", "");
		dontAddUpdation = false;	//If last statement of a process or main algorithm is a procedure call, then its updation statement must be added at the end
		
    }
    /**
     * It handles the subtree representing the return statement.
     * @param node
     */
    private void handleReturn(Node node)
    {
        String text = "[" + checkVariableAssignment("_stack") + " EXCEPT ![self] = Tail(" + checkVariableAssignment("_stack") + "[self])]";
        explodedTree.addStatement(currentLabelName, addAssignedVariableToVarList("_stack"), text);
        wasLastStatementCallReturnGoto = true;
    }


    /**
     * This function performs the translation of the for loop expanding it to ifthenelse statements and other auxiliary statements
		required for its representation in TLA+ language
     */


    private int handleForLoop(Node node, Node parentNode, int childNumber)
    {
        String iteratorID = node.getTextAt(2);
        String setExpression = handleExpression(node.jjtGetChild(0));
        String auxSetVar_idS = "idS_" + iteratorID;
        String pre_currentLoopLabel = currentLoopLabel;
        String loopLabel = currentLabelName;
		String pre_currentLabelName = currentLabelName;
		boolean pre_haveToReleaseLock = haveToReleaseLock;
		boolean isForNestedWithinLoop = false;	//If for is nested within loop and for is the last statement then it would have added updation statement
		
		currentLoopLabel = loopLabel;

        String errMsg = symTab.addSymbol(iteratorID, "variable", "0");
        if(!errMsg.equals(""))
        {
            handleError(3, node.getLineAndColumnNumber(1) + ":" + errMsg);
        }
        errMsg = symTab.addSymbol(auxSetVar_idS, "variable", "{}");
        if(!errMsg.equals(""))
        {
            handleError(3, node.getLineAndColumnNumber(1) + ":" + errMsg);
        }
        symTab.updateDeclarations();
        //Generating a unique idS variable for copying the
        //original set values. $
        
        //CHANGE the generateNewSymbol function BUG!!! generating a variable with old variable name.
        String auxSetVarComplete_idS = generateNewSymbol(auxSetVar_idS);

        
		if(currentProcessName.equals(("")) && currentMethodName.equals(""))
        {//if "for" belongs to main part of algorithm then variable should be added as a global variable.
            explodedTree.addVariable(iteratorID, "{}");
            globalVarList.put(iteratorID, "{}");
            explodedTree.addVariable(auxSetVarComplete_idS, "{}");
            globalVarList.put(auxSetVarComplete_idS, "{}");
        }
        
        String idS_lhs = auxSetVarComplete_idS;
        if(!currentProcessName.equals(""))
        {
            idS_lhs = auxSetVarComplete_idS.substring(0, auxSetVarComplete_idS.indexOf("["));
        }
        String idS_rhs = "";

        String condition = setExpression + " # {} /\\ " + checkVariableAssignment(auxSetVarComplete_idS) + " = {}";
        int numOfStatementsProcessed = 0;
        Map pre_varList = new HashMap();
        pre_varList.putAll(varList);

        isWithinForLoop = true;
        explodedTree.setIsForLoop(currentLabelName);
        explodedTree.addBranch(currentLabelName, false);
        explodedTree.addCase(currentLabelName, condition, false);
        idS_lhs = addForStatement(1, auxSetVarComplete_idS, setExpression, iteratorID);
        explodedTree.addUpdations(currentLabelName, "_pc", "[_pc EXCEPT ![self] = \"" + currentLabelName + "\"]");
        haveToReleaseLock = false;
		addUpdationInformation();
        
        //removeFromVarList(idS_lhs); 
        varList.clear();
        varList.putAll(pre_varList);
        
        explodedTree.addElse(currentLabelName);
            explodedTree.addBranch(currentLabelName, false);
            //condition = setExpression + " # {}";
            condition = auxSetVarComplete_idS + " # {}";

            explodedTree.addCase(currentLabelName, condition, false);
            idS_lhs = addForStatement(2, auxSetVarComplete_idS, setExpression, iteratorID);
            //setting global variables for storing the information of for loop
            String tmp_auxSetVar_idS_global = auxSetVar_idS_global;
            String tmp_setExpression_global = setExpression_global;
            String tmp_iteratorID_global = iteratorID_global;
            
            auxSetVar_idS_global = auxSetVar_idS;
            setExpression_global = setExpression;
            iteratorID_global = iteratorID;
            parentNode_global = parentNode;
            childNumber_global = childNumber;
			
			//The following 2 statements only find out the label's name after the for loop they do not make any changes to the exploded tree.
            numOfStatementsProcessed = handleRestOfStatements(parentNode, childNumber, true);
   			String labelAfterLoop = getLabelAfterLoop(parentNode, childNumber+numOfStatementsProcessed);
			if(labelAfterLoop.equals("Done"))
			{
				if(loopInfos.size() >= 1)	//current for loop is nested within any other for loop
				{
					loopInfo l = loopInfos.get(loopInfos.size()-1);
					labelAfterLoop = l.nextLabel;
				}
				else if(!pre_currentLoopLabel.equals(""))	//current for loop is not nested within any other for loop but we must confirm if it was nested within loop because that might be one reason we have received "Done" as a possible label after loop
				{
					labelAfterLoop = pre_currentLoopLabel;
					updationAddedbyFor = true;
		 		   isForNestedWithinLoop = true;
				}
				else if(!currentMethodName.equals("") && currentMethodType.equals("procedure"))
				{
					labelAfterLoop = createStackPCID();
				}
//				else
//					System.out.println("its done ................" + labelAfterLoop);
			}

			loopInfo li = new loopInfo();
			
			li.idSName = generateNewSymbol(auxSetVar_idS);
			li.iteratorID = iteratorID;
			li.loopLabel = loopLabel;
			li.nextLabel = labelAfterLoop;
			li.pNode = parentNode;
			li.cNumber = childNumber;
			li.releaseLock = pre_haveToReleaseLock;
			
			loopInfos.add(li);
			
			
            //body of for loop
            //handleBodyOfFor(node.jjtGetChild(1));
			handleBlock(node.jjtGetChild(1), "");		//Translates the set of statements inside for statement
	        isWithinForLoop = true;
			haveToReleaseLock= pre_haveToReleaseLock;

			//If last statement was not a loop statement, inside the for loop, then the auxiliary statement needs to be added
			//And if the last statement in the block of for loop was a branch then Auxiliary statements would already have been added.
			if(!wasLastLoopStatement && !branchFinished)
			{
				addAuxStatementsForForeach(0);			//Enters Auxillary statement of for statement after the last statement inside for statement
			}
			else if(wasSimpleLoopStatement && !branchFinished)
				//If last statement in the block of for loop was a loop statement the aux doesnt need to be added as it loops without condition
				//!branchFinished added because and extra updation information was being added at the end of the action
			{
				addUpdationInformation();
				wasSimpleLoopStatement = false;
			}
							
//			labelForStatementAfterLoop = labelAfterLoop;
			
//			System.out.println(">>>>>>>>>>>>>>>" + labelAfterLoop);
            
            //resetting the old values of global variables for storing the for loop information
            auxSetVar_idS_global = tmp_auxSetVar_idS_global;
            setExpression_global = tmp_setExpression_global;
            iteratorID_global = tmp_iteratorID_global;
            
            pre_currentLabelName = currentLabelName;
			currentLabelName = loopLabel;
			
			
            explodedTree.addElse(currentLabelName);

            varList.clear();
            varList.putAll(pre_varList);
            

	  		loopInfo removedLoopInfo = loopInfos.remove(loopInfos.size()-1);
			String nextlabel = "";
	  		if(loopInfos.size() > 0 )
			{
				loopInfo lastLoopInfo = loopInfos.get(loopInfos.size()-1);
				nextlabel = lastLoopInfo.nextLabel;
			}
			
			if(!(removedLoopInfo.nextLabel).equals(nextlabel))
			{
				handleRestOfStatements(parentNode, childNumber, false);
                explodedTree.addUpdations(currentLabelName, "_pc", generateNextPCRHS(labelAfterLoop));
                addUpdationInformation();
                removeFromVarList(auxSetVar_idS);			
			}
			else
			{
				if(loopInfos.size() > 0)
				{	
					if(numOfStatementsProcessed > 0)
						handleRestOfStatements(parentNode, childNumber, false);
					addAuxStatementsForForeach(1);	
				}
				else// Adds the else part for the second ifthenelse of the for loop statement
				{
		            numOfStatementsProcessed = handleRestOfStatements(parentNode, childNumber, false);
           		            explodedTree.addUpdations(currentLabelName, "_pc", generateNextPCRHS(labelAfterLoop));
					addUpdationInformation();	
				}
			}
			
			
				
				
            explodedTree.addEnd(currentLabelName, false);
        explodedTree.addEnd(currentLabelName, false);
		
		currentLabelName = pre_currentLabelName;

        isWithinForLoop = false;
        branchFinished = true;

        symTab.removeAuxVariable(iteratorID);
        symTab.removeAuxVariable(auxSetVar_idS);
        mustGenerateLabel = true;
        explodedTree.setCallReturnPCID(loopLabel, "\"" + loopLabel + "\"");
        currentLoopLabel = pre_currentLoopLabel;
		//Testing
		wasLastLoopStatement = true;
		wasForLoopStatement = true;
		if(isForNestedWithinLoop)
		{
			dontAddUpdation = true;
		}
			
		
  //      System.out.println("end of for loop: " + currentLabelName);
  
        return numOfStatementsProcessed;
    }
	/*
		This function generates the right have side of the _pc update statement 
		if the label start with "Head(_", it means its not the name of the label
		and the name of the label is stored at some other location.
		*/
	private String generateNextPCRHS(String lbl)
	{
		if(lbl.startsWith("Head(_"))
			return "[_pc EXCEPT ![self] = " + lbl + "]";
		else
			return "[_pc EXCEPT ![self] = \"" + lbl + "\"]";
	}
	/*
		This function adds the 3 different auxilliary statements of the "for" statement
		*/
    private String addForStatement(int num, String lhs, String rhs, String iterID)
    {
        String idS_lhs = "";
        if(currentMethodType.equals("procedure"))	
			/*In case for is used inside a procedure, then the auxilliary variables must be 
				accessed from the stack variable and its translation must be  different. */
        {
            idS_lhs = "_stack";
            switch(num)
            {
                case 1:
                    addNewHeadToStack(lhs, rhs, "_stack", generateAuxVariableStackStore(), "");
                    break;
                case 2:
                    explodedTree.addAuxStatement(currentLabelName, iterID, "CHOOSE fech \\in " + lhs + " : TRUE");
                    addNewHeadToStack(lhs, iterID, "_stack", generateAuxVariableStackStore(), iterID);
                    break;
                case 3:
                    addNewHeadToStack(lhs, checkVariableAssignment(lhs) + " \\ {" + checkVariableAssignment(generateNewSymbol(iterID)) + " }", checkVariableAssignment("_stack"), "__newhead", "");
                    break;

            }
 //           idS_lhs = checkVariableAssignment(idS_lhs);
        }
        else	//If for is not defined inside the procedure
        {
            idS_lhs = lhs;
            if(!currentProcessName.equals(""))
            {
				if(lhs.indexOf("[") > 0)	//Confirm that it contains square bracket
				{
                	idS_lhs = lhs.substring(0, lhs.indexOf("["));					
				}
				
            }
            switch(num)
            {
                case 1:
                	String temp2 = checkVariableAssignment(lhs);
                    addAssignedVariableToVarList(idS_lhs);
                    explodedTree.addAuxStatement(currentLabelName, checkVariableAssignment(idS_lhs), getRHSWithExcept(temp2, rhs));
                    break;
                case 2:
                	String iterID_chged = iterID;
                	if(currentProcessName.equals(""))
                	{
                		iterID_chged = "_" + iterID;
                		addAssignedVariableToVarList(iterID);
                	}
                    explodedTree.addAuxStatement(currentLabelName, iterID_chged, "CHOOSE fech \\in " + checkVariableAssignment(lhs) + " : TRUE");
                    if(!currentProcessName.equals(""))
                    {
                    	explodedTree.addAuxStatement(currentLabelName, "_" + checkVariableAssignment(idS_lhs), getRHSWithExcept(checkVariableAssignment(generateNewSymbol(iterID)), iterID));
                        addAssignedVariableToVarList(idS_lhs);
                    }
                    break;
                case 3:
                    explodedTree.addAuxStatement(currentLabelName, "_" + checkVariableAssignment(idS_lhs), getRHSWithExcept(checkVariableAssignment(lhs), checkVariableAssignment(lhs) + " \\ {" + checkVariableAssignment(generateNewSymbol(iterID)) + " }"));
                    addAssignedVariableToVarList(idS_lhs);
                    break;
            }
        }
        return idS_lhs;
    }
    /**
     *
     * @param lhs
     * @param rhs
     * @param stack
     * @param newhead
     */
    private void addNewHeadToStack(String lhs, String rhs, String stack, String newhead, String iterID)
    {
        String extension = "", rs = "";
        extension = lhs.substring(lhs.indexOf("."));
		
		if(iterID.equals(""))
			rs = "[" + newhead + " EXCEPT !" + extension + " = " + rhs + " ]";
		else
			rs = "[" + newhead + " EXCEPT !." + iterID + " = " + rhs + " ]";
			
        lhs = lhs.substring(0, lhs.indexOf("."));
        explodedTree.addAuxStatement(currentLabelName, newhead, lhs);
        explodedTree.addAuxStatement(currentLabelName, "_" + newhead, rs);
        rs = "[" + stack + " EXCEPT ![self] = Tail(" + stack + "[self]) ]";
        explodedTree.addAuxStatement(currentLabelName, "_" + stack, rs);
        addAssignedVariableToVarList("_stack");
        rs = "[_" + stack + " EXCEPT ![self] = Push(_" + stack + "[self], <<_" + newhead + ">>) ]";
        explodedTree.addAuxStatement(currentLabelName, "__" + stack, rs);
        addAssignedVariableToVarList("_stack");
		
    }
    /**
     * This function generate an auxillary variable for stack manipulation and store it to the list of auxillary variable for stack.
     * @return auxillary variable
     */
    private String generateAuxVariableStackStore()
    {
    	String var = generateStackAuxVariable();
    	auxVariablesStack.add(var);
    	return var;
    }
    private String generateStackAuxVariable()
    {
    	String nhead = "newHead";
    	boolean found = false;
    	int i = 1;
    	String var = nhead + i;
    	while(!found)
    	{
	    	if(varList.containsKey(var) || auxVariablesStack.contains(var))
	    	{
	    		var = nhead + i;
	    	}
	    	else
	    	{
	    		found = true;
	    	}
	    	i++;
    	}
    	return var;
    	
    }
    private String generateAuxVariable()
    {
    	String var = "i";
    	boolean found = false;
    	while(!found)
    	{
	    	if(varList.containsKey(var))
	    	{
	    		var += "i";
	    	}
	    	else
	    	{
	    		found = true;
	    	}
    	}
    	return var;
    }
    private int handleWith(Node node, Node parentNode, int childNumber)
    {
		isWithinWithBlock = true;
        String iteratorID = node.getTextAt(2);
        String setExpression = handleExpression(node.jjtGetChild(0));

        String errMsg = symTab.addSymbol(iteratorID, "variable", "0");
        if(!errMsg.equals(""))
        {
            handleError(3, node.getLineAndColumnNumber(1) + ":" + errMsg);
        }
		//Commenting the following lines for testing
        //symTab.updateDeclarations();
        //if(currentProcessName.equals(("")) && currentMethodName.equals(""))
        //{//if with belongs to main part of algorithm then variable should be added as a global variable.
        //    explodedTree.addVariable(iteratorID, "{}");
        //    globalVarList.put(iteratorID, "{}");
        //}
		
        //Adding to auxillary variable list
        currentAuxVariables.add(iteratorID);

        String lHS, rHS, completeVar, text;
        lHS = rHS = completeVar = text = "";
        completeVar = iteratorID; //generateNewSymbol(iteratorID); Changed because iterator variable for with is always location variable so its name does not need to be change according to the context
        if(completeVar.contains("["))
        {
        	text = completeVar.substring(0, completeVar.indexOf("["));
        }
        else
        {
        	text = completeVar;
        }
        lHS = text;
        String operatorUsed = node.getTextAt(3);
        int num = 0;
        String auxVar = generateAuxVariable();
		
		
        //If the operator used in with statement in \in then it should add a proper existential statement
        if(!operatorUsed.equals("="))
        {
        	explodedTree.addWithStatement(currentLabelName, "", "\\E " + completeVar + " \\in " + setExpression + ":");
            lHS = generateNewSymbol(iteratorID);
            rHS = getRHSWithExcept(lHS, auxVar);
            if(completeVar.contains("["))
            {
            	lHS = lHS.substring(0, lHS.indexOf("["));
            }
        }
        else//if the operator used is = then is should simply prepare a LETIN statement
        {
        	rHS = getRHSWithExcept(completeVar, setExpression);
        }
				
		//To be tested yet
        if(lHS.startsWith("Head("))
        {
            addNewHeadToStack(completeVar, auxVar, checkVariableAssignment("_stack"), generateAuxVariableStackStore(), "");
            addAssignedVariableToVarList(lHS);
        }
		
        //Adds a LETIN statement 
		if(operatorUsed.equals("="))
        {
        	/*
            if(completeVar.contains("["))
            {
                String extension = completeVar.substring(completeVar.indexOf("["), completeVar.length());
                rHS = "["+text+" EXCEPT !"+extension+" = " + setExpression + "]";
            }
            else
            {
                rHS = setExpression;
            }
            */
            //Commented addAssignedVariableToVarList(lHS);
            explodedTree.addStatement(currentLabelName, lHS, rHS);
//			System.out.println(" here is it>>>>>>>>>>" + rHS);
        }
		//Translates the set of statements inside the with statement
        isBlockOfLoop = true;
		handleBlock(node.jjtGetChild(1), "");
        isBlockOfLoop = false;
		/*
        String pre_lhs = checkVariableAssignment(generateNewSymbol(iteratorID));

        //if with statement contains branch then
        /*
        System.out.println(branchFinished);
        if(branchFinished)
        {System.out.println("********here**********");
            explodedTree.insertAuxVariableInitializationStatement(currentLabelName, checkVariableAssignment(lHS));
        }
         * */
        //explodedTree.addStatement(currentLabelName, checkVariableAssignment(lHS), getRHSWithExcept(pre_lhs, "0"));
        //varList.put(completeVar, "0");

        /* it aux var is defined in main algo rithm then its different
        String new_lhs = checkVariableAssignment(lHS);
        addAssignedVariableToVarList(new_lhs);
        explodedTree.addStatement(currentLabelName, "_" + new_lhs, 0);
         * */
	 	if(wasLastBranch)
	 		dontAddUpdation = true;
		
        symTab.removeAuxVariable(iteratorID);
        mustGenerateLabel = true;
        currentAuxVariables.remove(currentAuxVariables.size()-1);
		isWithinWithBlock = false;
        return num;
    }

    private String getRHSWithExcept(String var, String originalRHS)
    {
        String rhs = "";
        if(var.contains("["))
        {
            String extension = var.substring(var.indexOf("["), var.length());
            rhs = "["+var.substring(0, var.indexOf("["))+" EXCEPT !"+extension+" = " + originalRHS + "]";
        }
        else
        {
            rhs = checkVariableAssignment(originalRHS);
        }
        return rhs;
    }

	    /**
	     * This function get the possible next label after the loop.
	     * @param parentNode  The node in which the statement is 
	     * @param childNumber  statement number from where we need to find the label
	     * @return possible label/Done if its the last statement of the a possible block
	     */
    private String getLabelAfterLoop(Node parentNode, int childNumber)
    {
        int numChildren = parentNode.jjtGetNumChildren();
        Node child = null;
        int i = childNumber+1;
        String colon = ":";
        String label = "Done";
        if(i < numChildren)	//If there are statements after the current loop
        {
            child = parentNode.jjtGetChild(i);

            if(colon.compareTo(child.getTextAt(2)) == 0)
            {
                label = child.getTextAt(1);
            }
            else
            {
                Node childInstruction = child.jjtGetChild(0).jjtGetChild(0);
                String instructionName = childInstruction.toString();
				if(instructionName.equals("atomic"))
				{
					label = getFirstStatementsLabelInBlock(childInstruction);
					if(label.equals(""))
					{
		                label = generateNewLabelAndAddToList(child.getLineNumber());
					}
				}
				else
				{
	                label = generateNewLabelAndAddToList(child.getLineNumber());
				}
            }
        }
        else 	//If there arent any statements after the current loop
        {
			Node pNode = parentNode.jjtGetParent();
			//n.dump(">>");
			String pNodeName = pNode.toString();
			
			if(pNodeName.equals("atomic"))
			{
				Node nd = ((pNode.jjtGetParent()).jjtGetParent()).jjtGetParent();
				int cNum = nd.jjtGetChildNumber((pNode.jjtGetParent()).jjtGetParent());
				String laloop = getLabelAfterLoop(nd, cNum);
//	            System.out.println("ITS : " + laloop);
				label = laloop;
			}
			else if(pNodeName.equals("branchArm"))
			{
				Node bNode = pNode.jjtGetParent();
				Node nd = (((pNode.jjtGetParent()).jjtGetParent()).jjtGetParent()).jjtGetParent();
				int cNum = nd.jjtGetChildNumber(((pNode.jjtGetParent()).jjtGetParent()).jjtGetParent());
				String laloop = getLabelAfterLoop(nd, cNum);
//	            System.out.println("ITS AFTER BRANCH: " + cNum);
//	            System.out.println("ITS AFTER BRANCH: " + nd.toString() + " label is : " +laloop);
				label = laloop;
				
			}
			else if(pNodeName.equals("loop"))
			{
				//label = currentLoopLabel;		commented because for enclosed inside a loop was not generating correct next pc labels requires testing of atomic statement again
			}
        }
        return label;
    }
	
	private String getFirstStatementsLabelInBlock(Node block)
	{
		String label= "";
		String colon = ":";
		
		Node firstStatement = (block.jjtGetChild(0)).jjtGetChild(0);
		if(colon.equals(firstStatement.getTextAt(2)))
		{
			label = firstStatement.getTextAt(1);
		}
				
		return label;
	}
    private int handleRestOfStatements(Node parentNode, int childNumber, boolean returnCount)
    {
        int numChildren = parentNode.jjtGetNumChildren();
        Node child = null;
        int numOfStatementsProcessed = 0;
        
        for(int i=childNumber+1;i<numChildren;i++)
        {
            child = parentNode.jjtGetChild(i);
            numOfStatementsProcessed ++;

            if(child.jjtGetNumChildren() > 1)	//If a statement has a label then it should immediately stop.
            {
                numOfStatementsProcessed = i - childNumber - 1;
                break;
            }
            else		//Only unlabeled assignment statements are processed to be part of the for statement
            {
                Node Instruction = child.jjtGetChild(0);
                Node childInstruction = child.jjtGetChild(0).jjtGetChild(0);
                String instructionName = childInstruction.toString();
                if(instructionName.compareTo("assignSingle") == 0)
                {
                    if(!returnCount)
					{
						int numOfChildren = Instruction.jjtGetNumChildren();
                    	for(int j=0;j<numOfChildren;j++)
                    	{
                        	childInstruction = Instruction.jjtGetChild(j);
                        	handleAssignment(childInstruction);
                    	}
					}
                }
                else if(instructionName.compareTo("skip") == 0)
                {
                }
                else if(instructionName.compareTo("print") == 0)
                {
                    if(!returnCount)
					{
                    	handlePrint(Instruction);
					}
                }
                else
                {
                    numOfStatementsProcessed = i - childNumber - 1;
                    break;
                }
                
            }
        }
        return numOfStatementsProcessed;
    }
	private void addAuxStatementsForForeach(int j)
	{
		if(loopInfos.size() >= 1)
		{
			//loopInfo l = loopInfos.get(loopInfos.size()-1);
			//labelAfterLoop = l.nextLabel;
		   for (int i = loopInfos.size()-1 ; i>= 0;i--) 
	   		{
				loopInfo l = loopInfos.get(i);
				//System.out.println(l.idSName + " : " + l.releaseLock);
				addAux(l.idSName , l.iteratorID, l.loopLabel, l.pNode,  l.cNumber, l.releaseLock);
				if(i>0)
				{
					loopInfo pl = loopInfos.get(i-1);
					if(!(pl.nextLabel).equals(l.nextLabel))
					{
		                explodedTree.addUpdations(currentLabelName, "_pc", generateNextPCRHS(l.nextLabel));
						if(l.releaseLock)	//Adds release lock statement for the atomic
						{
							boolean pre_haveToReleaseLock = haveToReleaseLock;
							haveToReleaseLock = true;
			                addUpdationInformation();
							haveToReleaseLock = pre_haveToReleaseLock;
						}
						else
							addUpdationInformation();
		                removeFromVarList(l.idSName);
		            explodedTree.addEnd(currentLabelName, false);
		            branchFinished = true;
					return;
					}
				}
				else
				{		explodedTree.addUpdations(currentLabelName, "_pc", generateNextPCRHS(l.nextLabel));
						if(l.releaseLock)	//Adds release lock statement for the atomic
						{
							boolean pre_haveToReleaseLock = haveToReleaseLock;
							haveToReleaseLock = true;
							//System.out.println(haveToReleaseLock);
	     					addUpdationInformation();
							haveToReleaseLock = pre_haveToReleaseLock;
						}
						else
							addUpdationInformation();
		                removeFromVarList(l.idSName);
		            explodedTree.addEnd(currentLabelName, false);
		            branchFinished = true;
				}
				
	        }
			
		}
	}
    private void addAux(String auxSetVar_idS, String iteratorID, String loopLabel, Node parentNode, int childNumber, boolean releaseLock)
    {
        String idS_lhs = addForStatement(3, auxSetVar_idS, "", iteratorID);
				
        //System.out.println(idS_lhs + ":" + auxSetVar_idS  + ":" + iteratorID  + ":" + labelAfterLoop);
		
//		Thread.currentThread().dumpStack();
        if(!wasLastStatementProcedureCall)// && !wasLastStatementCallReturnGoto)
        {
            explodedTree.addBranch(currentLabelName, false);
            String condition = checkVariableAssignment(generateNewSymbol(auxSetVar_idS)) + " # {}";
            explodedTree.addCase(currentLabelName, condition, false);
                explodedTree.addUpdations(currentLabelName, "_pc", "[_pc EXCEPT ![self] = \"" + loopLabel + "\"]");
				boolean pre_haveToReleaseLock = haveToReleaseLock;
				haveToReleaseLock = false;
				addUpdationInformation();
				haveToReleaseLock = pre_haveToReleaseLock;

            explodedTree.addElse(currentLabelName);
                //statements after for loop
                handleRestOfStatements(parentNode, childNumber, false);
									
                //explodedTree.addUpdations(currentLabelName, "_pc", "[_pc EXCEPT ![self] = \"" + labelAfterLoop + "\"]");
                //addUpdationInformation();
                //removeFromVarList(idS_lhs);
            //explodedTree.addEnd(currentLabelName);
            branchFinished = true;
        }
		
		
        else//NEEDS to be updated as previous condition
        {
			System.out.println("You have commented some code out!!!!!" + currentLabelName);
			//Commented because its not updated yet and it was adding an extra label that was not required in case of a break inside a for loop
			/*
        	String pre_currentLabelName = currentLabelName;
        	currentLabelName = generateNewLabel(parentNode_global.jjtGetChild(childNumber_global).getLineNumber());
            explodedTree.addBranch(currentLabelName, false);
            String condition = checkVariableAssignment(generateNewSymbol(auxSetVar_idS_global)) + " # {}";
            explodedTree.addCase(currentLabelName, condition, false);
                explodedTree.addUpdations(currentLabelName, "_pc", "[_pc EXCEPT ![self] = \"" + pre_currentLabelName + "\"]");
                addUpdationInformation();
            explodedTree.addElse(currentLabelName);
                //statements after for loop
                handleRestOfStatements(parentNode_global, childNumber_global, false);
                addUpdationInformation();
                removeFromVarList(idS_lhs);
            explodedTree.addEnd(currentLabelName);
            branchFinished = true;
//            currentLabelName = pre_currentLabelName;
				*/
        }
    }
    /**
     * It handles the sub tree representing the branch statement.
     * @param node
     */
    private void handleBranch(Node node, boolean isIfelse)
    {
//		System.out.println(" -------------- branch starting ----------------- ");
    	if(node.jjtGetNumChildren() == 0)
    	{
    		addAuxStatementsForForeach(0);
    		return;
    	}
		boolean isLastStatementOfBlock_local = isLastStatementOfBlock;
		//These variables are used to retain the previous values of global variables during nested branch statements 
        boolean previous_isWithinBranch = isWithinBranch;
        boolean previous_isBlockOfBranch = isBlockOfBranch;
		boolean pre_haveToAcquireLock = haveToAcquireLock;
		boolean pre_haveToReleaseLock = haveToReleaseLock;
        Map pre_varList = new HashMap();
        String negationOfAllIfConditions = "";
        
        pre_varList.putAll(varList);
        
        String branchLabel = currentLabelName;	

        explodedTree.addBranch(branchLabel, true); //Adds a branch statement to the eTree.
        //Iterates over all the branch arms
		for(int i=0;i<node.jjtGetNumChildren();i++)
        {
            Node child = node.jjtGetChild(i);
            String name = child.toString();
			haveToAcquireLock = pre_haveToAcquireLock;
			haveToReleaseLock = pre_haveToReleaseLock;
            if(name.equals("branchArm") || name.equals("expression") || (name.equals("statements") && isIfelse))
            {

                Node expNode = null;
                Node blockNode = null;
                String condition = "";
                boolean bodyExists = true;
                //This if else prepares the condition statement and identifies the block of statements of the branch arm
				if(name.equals("statements")) //If its the else part of the branch then negation of all the above statements must be added
                {
                	negationOfAllIfConditions = "~(" + negationOfAllIfConditions + ")";
                    blockNode = child;
                    condition = negationOfAllIfConditions;
                }
                else if(name.equals("expression"))
                {
                    expNode = node.jjtGetChild(0);
                    if(node.jjtGetNumChildren() > 1)
                    {
                        blockNode = node.jjtGetChild(1);
                        i++;
                    }
                    else
                    {
                        bodyExists = false;
                    }
                    condition = handleExpression(expNode);
                }
                else
				{
                    expNode = child.jjtGetChild(0);
                    blockNode = child.jjtGetChild(1);
                    condition = handleExpression(expNode.jjtGetChild(0));
                }
//				System.out.println("At : " + currentLabelName + " Printing something i assume to be token : " + blockNode.doesBlockNotContainsLabel());
				if(blockNode != null)
					if(blockNode.doesBlockNotContainsLabel())
					{
						haveToAcquireLock = false;
						haveToReleaseLock = false;
					}
				//When the condition and block is identified, the condition is added to the eTree.
                explodedTree.addCase(branchLabel,condition, true);
                //Prepares the conditions for negation
				if(i > 0)
                {
                    negationOfAllIfConditions += " \\/ ";
                }
                negationOfAllIfConditions += condition;
				
                isWithinBranch = true;
                isBlockOfBranch = true;
                currentLabelName = branchLabel;
                branchFinished = false;
                wasLastStatementCallReturnGoto = false;
                if(bodyExists)
                {
                    handleBlock(blockNode, "");
                }
                if(!branchFinished)
				{
					if(isWithinForLoop && isLastStatementOfBlock_local)
						addAuxStatementsForForeach(0);			//Enters Auxillary statement of for statement after the last statement inside for statement
					else
					{
						addUpdationInformation();
					}
                }
            }
            else
            {
                negationOfAllIfConditions = "~(" + negationOfAllIfConditions + ")";
                explodedTree.addCase(branchLabel,negationOfAllIfConditions, true);
                isWithinBranch = true;
                isBlockOfBranch = true;
                currentLabelName = branchLabel;
                branchFinished = false;
                wasLastStatementCallReturnGoto = false;
//				System.out.println("Printing something i assume to be token : " + child.doesBlockNotContainsLabel());
				if(child.doesBlockNotContainsLabel())
				{
					haveToAcquireLock = false;
					haveToReleaseLock = false;
				}
                handleBlock(child, "");
                if(!branchFinished)
                {
					if(isWithinForLoop && isLastStatementOfBlock_local)
						addAuxStatementsForForeach(0);			//Enters Auxillary statement of for statement after the last statement inside for statement
					else
 					   addUpdationInformation();
                }
            }
            varList.clear();
            varList.putAll(pre_varList);
            explodedTree.setPCID(currentLabelName, createPCID());
        }
		haveToAcquireLock = pre_haveToAcquireLock;
		haveToReleaseLock = pre_haveToReleaseLock;
		

        currentLabelName = branchLabel;
        isWithinBranch = previous_isWithinBranch;
        isBlockOfBranch = previous_isBlockOfBranch;
        explodedTree.addEnd(branchLabel, true);
        branchFinished = true;
		wasLastBranch = true;
		
    }
	
	
    /**
     * It handles the sub tree representing the goto statement. The goto statement 
		
     * @param node
     */
    private void handleGoto(Node node)
    {
        String lhs, rhs;
        lhs = rhs = "";
        lhs = createPCID();
        
        if(isWithinBranch)
        {
            rhs = "[_pc EXCEPT ![self] = \"" + node.getTextAt(2) + "\"]";
            explodedTree.addUpdations(currentLabelName, "_pc", rhs);
            //wasLastStatementCallReturnGoto = true;
        }
        else
        {
            rhs = "\"" + node.getTextAt(2) + "\"";
            explodedTree.setNextPC(currentLabelName, rhs);
            explodedTree.setPCID(currentLabelName, createPCID());
        }
        //isWithinBranch = false;
		wasLastStatementCallReturnGoto = true;
    }
    /**
     * It generates new ID for the pc variable.
     * @return  It returns new PC ID.
     */
    private String createPCID()
    {
        String pdID = "";
        pdID = "_pc[self]";
        return pdID;
    }
    /**
     * It generates new ID for the pc variable for stack.
     * @return  It returns new stack PC ID.
     */
    private String createStackPCID()
    {
        String stackID = "";
        stackID = "Head(_stack[self])._pc";
        /*
        if(currentMethodName.compareTo("") == 0 || currentProcessName.compareTo("") == 0)
            stackID = "_stack._pc";
        else if(currentMethodType.compareTo("process") == 0 ||(currentMethodType.compareTo("function") == 0 && currentProcessName.compareTo("") != 0))
            stackID = "_" + currentProcessName + "_stack[self]._pc";
        else if(currentMethodType.compareTo("thread") == 0)
            stackID = "_" + currentProcessName + "_" + currentMethodName + "_stack[self]._pc";
         * */
        return stackID;
    }
    /**
     * It handles the sub tree representing a loop statement.
     * @param node : part of the tree
     * @param firstLabelAfterLoop : Label attached to the statement following the loop statement.
     */
    private void handleLoop(Node node, String firstLabelAfterLoop)
    {
       String pre_labelAfterLoopForBreakStatement = labelAfterLoopForBreakStatement;
	   
	   //Following 2 statements ignore that they current loop is inside for loop if in case it is.
	   //For the moment you can have a loop inside for loop but the break statement wont know that there was a for loop outside it.
	   //However it would definitely work with loop
	   boolean pre_isWithinForLoop =isWithinForLoop;
	   isWithinForLoop = false;
       
	   boolean pre_isBlockOfLoop = isBlockOfLoop;
       labelAfterLoopForBreakStatement = firstLabelAfterLoop;

       String loopLabel = "";
        
       //Adds a label to the loop statement if it doesnt have one
	   if(!currentStatementHasLabel)
       {
            currentLabelName = generateNewLabel(node.getLineNumber());
            currentStatementHasLabel = true;
       }
       loopLabel = currentLabelName;
       String pre_currentLoopLabel = currentLoopLabel;
       currentLoopLabel = loopLabel;
       isBlockOfLoop = true;
       
	   //Translates the statements inside the loop by recurrsively calling the function handleBlock(..)
	   handleBlock(node.jjtGetChild(0), "");
	   
	   //If the last statement inside the loop statement was a branch then the updation statements would definitely be there
	   //otherwise they must be added
	   if(wasLastBranch)
		   dontAddUpdation = true;
		
	   
	   //to be completed
	   if(!branchFinished)
       {
           // addUpdationInformation();
       }
	   
       isBlockOfLoop = false;
	   //If last statement of a loop was a jump to another label then loop wont be there anymore
	   if(!wasLastStatementCallReturnGoto && !updationAddedbyFor)
       		explodedTree.setNextPC(currentLabelName, "\""+loopLabel+"\"");
       explodedTree.setPCID(currentLabelName, createPCID());

       labelAfterLoopForBreakStatement = pre_labelAfterLoopForBreakStatement;
	   
       if(firstLabelAfterLoop.equals("Done") || firstLabelAfterLoop.equals(createStackPCID()))
       {
            labelForStatementAfterLoop = "";
//            wasLastLoopStatement = false;
       }
       else
       {
            labelForStatementAfterLoop = firstLabelAfterLoop;
//            wasLastLoopStatement = true;
       }
       wasLastLoopStatement = true;
       
	   if(branchFinished && !updationAddedbyFor)
       {
           explodedTree.setAllNextPC(currentLabelName, "\""+ currentLoopLabel +"\"");
       }
       
	   if(!pre_currentLoopLabel.equals(""))
       {
            currentLoopLabel = pre_currentLoopLabel;
       }
	//   else		//Sabina:Please check if it creates any issue
	//	   currentLoopLabel = "";
       isBlockOfLoop = pre_isBlockOfLoop;
	   wasSimpleLoopStatement = true;
	   isWithinForLoop = pre_isWithinForLoop;
	   updationAddedbyFor = false;
    }
    /**
	 * SABINA: REMOVE this function 
     * This function adds a statement that reinitializes the auxiliary variables used in with and for loops.
     */
    private void insertAuxVarInitializationStatement()
    {
        String auxVar = currentAuxVariables.get(currentAuxVariables.size()-1);
        String auxVar_comp = checkVariableAssignment(generateNewSymbol(auxVar));
        if(currentMethodType.equals("procedure"))
        {
        	//addNewHeadToStack(auxVar_comp, "0", checkVariableAssignment("_stack"), generateAuxVariableStackStore(), false);        
        }
        else if(!currentProcessName.equals(""))
        {
        	addAssignedVariableToVarList("_" + currentProcessName + "_data");
            explodedTree.addAuxStatement(currentLabelName, checkVariableAssignment("_" + currentProcessName + "_data"), getRHSWithExcept(auxVar_comp, "0"));
        }
        else
        {
        	explodedTree.addAuxStatement(currentLabelName, auxVar_comp, "0");
        }
    }
    /**
     * It handles the sub tree representing an assignment statement.
     * @param node
     */     				
		
    private void handleAssignment(Node node)
    {
        if(node.jjtGetNumChildren() == 0)
        {
			System.out.println("Remove this condition from here");
			//		explodedTree.addAuxStatement(currentLabelName, "I am", "TRYING");

			//SABINA: FIXIT it added aux variable reinitialization statement remove this issue from the jjt file
            //insertAuxVarInitializationStatement();
            return;
        }
        Node child, rhsChild;
        String rHS, exp, lHS[];
     
        exp = "";
        
        child = rhsChild = node.jjtGetChild(1);
        rHS = rhsChild.toString();
        
        if(rHS.compareTo("expression") == 0)
        {	
            exp = handleExpression(rhsChild.jjtGetChild(0));
        }
        else
        {
            System.out.println("its function call with assignment");
        }
        
        child = node.jjtGetChild(0);
        lHS = handleLHS(child);
		//SABINA: require confirmation the parameters are correct
		symTab.checkDeclaration(child.getTextAt(1), "variable", 0, node.getLineAndColumnNumber(1));   
		
        
        if(lHS[2].compareTo("") != 0)
        {
            String symbol = lHS[0];
            //String stack = symbol.substring(4, symbol.indexOf(")")+1);
            String stack = checkVariableAssignment("_stack");
            String extension = symbol.substring(symbol.indexOf("."));
            String rhs = symbol.substring(0, symbol.indexOf(")")+1);
            //FIX Aux statements
            explodedTree.addStatement(currentLabelName, checkVariableAssignment("_newhead"), rhs);
            rhs = "[" + checkVariableAssignment("_newhead") + " EXCEPT !" + extension + " = " + exp + " ]";
            addAssignedVariableToVarList("_newhead");
            explodedTree.addStatement(currentLabelName, checkVariableAssignment("_newhead"), rhs);
            
            rhs = "[" + stack + " EXCEPT ![self] = Tail(" + stack + "[self]) ]";
            
            explodedTree.addStatement(currentLabelName, "_" + stack, rhs);
            addAssignedVariableToVarList("_stack");
            rhs = "[_" + stack + " EXCEPT ![self] = Push(_" + stack + "[self], <<" + checkVariableAssignment("_newhead") + ">>) ]";
            explodedTree.addStatement(currentLabelName, "__" + stack, rhs);
            addAssignedVariableToVarList("_stack");
            addAssignedVariableToVarList("_newhead");
            //stackUpdatedAddLabel = true;
            
        }
        else if(lHS[1].compareTo("") != 0)
        {
            lHS[1] = lHS[1] + exp + "]";
            explodedTree.addStatement(currentLabelName, lHS[0], lHS[1]);           
        }
        else
        {	
            explodedTree.addStatement(currentLabelName, lHS[0], exp);
        }
    }
    /**
     * It handles the sub tree representing the left-hand side of the statement.
     * @param node
     * @return      It returns the corresponding left-hand side.
     */
    private String[] handleLHS(Node node)
    {
        String stackName = "";
        String text = node.getTextAt(1);
        String newSymbol[] = new String[3];
        String completeVar = node.reproduceText();

        newSymbol[0] = generateNewSymbol(text);
        newSymbol[1] = "";
        newSymbol[2] = "";             		

        if(newSymbol[0].startsWith("Head("))
        {
            String extension = "";
            newSymbol[2] = "Head";
            if(completeVar.contains("["))
            {
                extension = completeVar.substring(completeVar.indexOf("["));
                extension = "[" + handleExpression(((node.jjtGetChild(0)).jjtGetChild(0)).jjtGetChild(0)) + "]";
                newSymbol[0] += extension;
            }
            else if(completeVar.contains("."))
            {
                extension = completeVar.substring(completeVar.indexOf("."));
                newSymbol[0] += extension;
            }
        }
        else if(newSymbol[0].contains("["))
        {
            stackName = newSymbol[0].substring(0, newSymbol[0].indexOf("["));
            String extension = newSymbol[0].substring(newSymbol[0].indexOf("["));
            if(varList.containsKey(stackName))
                newSymbol[1] = "["+varList.get(stackName)+" EXCEPT !"+extension;
            else
                newSymbol[1] = "["+stackName+" EXCEPT !"+extension;
            
            if(completeVar.contains("["))
            {
                extension = completeVar.substring(completeVar.indexOf("["));
                extension = "[" + handleExpression(((node.jjtGetChild(0)).jjtGetChild(0)).jjtGetChild(0)) + "]";
                newSymbol[1] += extension;
            }
            else if(completeVar.contains("."))
            {
                extension = completeVar.substring(completeVar.indexOf("."));
                newSymbol[1] += extension;
            }
            newSymbol[1] += " = ";
        }
        else
        {
            text = checkVariableAssignment(text);           
            if(completeVar.contains("["))
            {
                String extension = completeVar.substring(completeVar.indexOf("["));
                extension = handleExpression(node.jjtGetChild(0));		//Translation of variable like Func[a,b] on the left-hand side of the assignment statement
                newSymbol[1] = "["+text+" EXCEPT !"+extension+" = ";
            }
            else if(completeVar.contains("."))
            {
                String extension = completeVar.substring(completeVar.indexOf("."));
                newSymbol[1] = "["+text+" EXCEPT !"+extension+" = ";
            }
        }
        if(!stackName.equals(""))
            newSymbol[0] = stackName;
        if(newSymbol[2].equals("")){        	
            newSymbol[0] = addAssignedVariableToVarList(newSymbol[0]);        	
        }
        return newSymbol;
    }
    
    /* CONTAINS AN INFINITE LOOP MUST BE CHANGED */
    String helpHandleDefinition (Node node){
    	int i = 1;
    	String text = "";
    	int k = 1;
    	    	
    	boolean aux = false;
    	
    	while (i != 0){
    		if(node.getTextAt(k).equals("[")){
    			i++;
    			//if (node.getTextAt(k-1).equals("!") || node.getTextAt(k-1).equals("]"))
    			if(!node.getTextAt(k-1).equals("="))
    				text = text + node.getTextAt(k);
    			else
    				text = text + " " + node.getTextAt(k);
    			aux = true;}
    		else if(node.getTextAt(k).equals("]")){
    				i--;
    				text = text.substring(0, text.length()) + node.getTextAt(k);}
    		else if(node.getTextAt(k).equals("(")){
    			text = text + node.getTextAt(k);
    			aux = true;}
    		else if(node.getTextAt(k).equals(")")){
    			text = text.substring(0, text.length()) + node.getTextAt(k);
    			}
    		else if(node.getTextAt(k).equals(",")){ 
    				text = text.substring(0, text.length()) + ",";
    				aux = true;
    			 }
    		else
    			if (aux) {
    				text = text + node.getTextAt(k);
    				aux = false;}
    			else
    				text = text + " " + node.getTextAt(k);	
    		k++;    		
    	}
    	
    	return text;
    }
	private String handleProcessNameForQuantification(Node node, String boundVariable, ArrayList<String> boundVariables, String pName)
	{
		if(boundVariables.size() > 1)	//If there are more than one bound variables
		{
			for(int j=0;j<boundVariables.size();j++)
			{
				if(listOfQuantVars.containsKey(boundVariables.get(j)))
					handleError(7, "Syntax Error: Bound variable already exists \"" + boundVariables.get(j) + "\" used at " + node.getLineAndColumnNumber(1));
				listOfQuantVars.put(boundVariables.get(j), listOfAllProcessIDs.get(pName));
			}
		}
		else	//If there's only one bound variable
		{
			if(listOfQuantVars.containsKey(boundVariable))
				handleError(7, "Syntax Error: Bound variable already exists \"" + boundVariable + "\" used at " + node.getLineAndColumnNumber(1));
			listOfQuantVars.put(boundVariable, listOfAllProcessIDs.get(pName));
		}

		return listOfAllProcessIDs.get(pName);
		
	}
	private String handleExtendedProcessNameForQuantification(Node node, String boundVariable, ArrayList<String> boundVariables, String pNameorSet)
	{
		String pName = pNameorSet.substring(pNameorSet.lastIndexOf(".")+1);	
		String qVarName = pNameorSet.substring(0, pNameorSet.lastIndexOf("."));	
		if(listOfQuantVars.containsKey(qVarName))
		{
			String parentName = listOfQuantVars.get(qVarName);
			if(listOfAllProcessIDs.get(pName) != null)
			{
				if(symTab.getParentName(pName) != null)
				{
					if(!parentName.equals(symTab.getParentName(pName)))
					{
						//Add warning that the quantification variable used does not represent the parent process
						handleError(7, "Syntax Error: \"" + parentName + "\" is not the parent process of \"" + pName + "\" " + node.getLineAndColumnNumber(1) + ".");
					//listOfWarnings += "Warning: \"" + parentName + "\" is not the parent process of \"" + pName + "\" " + boundNode.getLineAndColumnNumber(1) + ".\r\n";
					}
				}
				pNameorSet = pName;	
				if(conditionStringForProperty.equals(""))
				{
					conditionStringForProperty = "(";
				}
				
				if(boundVariables.size() > 1)	//If there are more than one bound variables
				{
					for(int j=0;j<boundVariables.size();j++)
					{
						if(listOfQuantVars.containsKey(boundVariables.get(j)))
							handleError(7, "Syntax Error: Bound variable already exists \"" + boundVariables.get(j) + "\" used at " + node.getLineAndColumnNumber(1));
						listOfQuantVars.put(boundVariables.get(j), listOfAllProcessIDs.get(pName));		
						conditionStringForProperty += qVarName + " = " + "_" + pName + "_data[" + boundVariables.get(j) + "].parentID /\\ ";									
					}
				}
				else	//If there's only one bound variable
				{
					if(listOfQuantVars.containsKey(boundVariable))
						handleError(7, "Syntax Error: Bound variable already exists \"" + boundVariable + "\" used at " + node.getLineAndColumnNumber(1));
					listOfQuantVars.put(boundVariable, listOfAllProcessIDs.get(pName));		
					conditionStringForProperty += qVarName + " = " + "_" + pName + "_data[" + boundVariable + "].parentID /\\ ";
				}
			}
			else
			{//Add warning that the process name used is not a valid process's name 
				handleError(7, "Syntax Error: Process name \"" + pName + "\" is not a valid name used at " + node.getLineAndColumnNumber(1) + ".");
				//listOfWarnings += "Warning: Process name \"" + pName + "\" is not a valid name used at " + node.getLineAndColumnNumber(1) + ".\r\n";
			}
		}
		else
		{	//Add warning that the quantification variable used is not defined as a bound variable
			handleError(7, "Syntax Error: Variable \"" + qVarName + "\" is not defined as a bound variable used at " + node.getLineAndColumnNumber(1) + ".");
			//listOfWarnings += "Error: Variable \"" + qVarName + "\" is not defined as a bound variable used at " + node.getLineAndColumnNumber(1) + ".\r\n";
		}
	
		return listOfAllProcessIDs.get(pNameorSet);
	}
	
	private String handleQuantificationExpression(Node node)
	{
			String exp = "";
            exp = node.getTextAt(1) + " ";			
            Node boundsNode = node.jjtGetChild(0);
            String boundVariable = "";
		    ArrayList<String> boundVariables = new ArrayList<String>();
			
            for(int i=0;i<boundsNode.jjtGetNumChildren();i++)
            {
				boundVariables.clear();
				if(i > 0)
					exp += ", ";
				
                Node boundNode = boundsNode.jjtGetChild(i);
                Node expNode = boundsNode.jjtGetChild(i);
                boolean check = true;
                String operator_in = "\\in";
	            int k = 1;
				String tk = boundNode.getTextAt(k);
                while(!tk.equals(operator_in))
                {
					if(tk.equals(","))
						exp += ", ";
					else
					{
	                    exp += boundNode.getTextAt(k);
					
	                    boundVariable = boundNode.getTextAt(k);
						boundVariables.add(boundVariable);
                    
						if(!isExpressionForProperty)
	                    {
	                    	symTab.addSymbol(boundVariable, "variable", "");
	                    }
	                    else
	                    {
	                    	symTab.addSymbol(boundVariable, "aux", "");
	                    }
					}
					k = k + 1;
					tk = boundNode.getTextAt(k);
                }
				
				//To be restated: Assuming that the quantification expression for writing properties will always have 
				//the name of the process or ... and it does not require translation using handleExpression.
				String pNameorSet = (boundNode.jjtGetChild(0)).reproduceText();
		        String scope[] = symTab.getScopeInformation(pNameorSet, "variable", 0);				
				
				if(isExpressionForProperty){					
					if(isAlgorithmLevelProperty){
						if(listOfAllProcessIDs.get(pNameorSet) != null && symTab.getParentName(pNameorSet) == "")
						{
							pNameorSet = handleProcessNameForQuantification(node, boundVariable, boundVariables, pNameorSet);
						}
						else if(pNameorSet.contains("."))
						{
							pNameorSet = handleExtendedProcessNameForQuantification(boundNode, boundVariable, boundVariables, pNameorSet);
						}
						else if(scope[1].equals("algorithm"))
						{
							//Allows quantification over global variables (it is required in the case of a set) 
							//For the moment compiler only allows at algorithm level
							//Requires translation of properties to be redefined
						}
						else
						{	
							handleError(7, "Syntax Error: The process name is incorrect/incorrectly refered in the property at " + node.getLineAndColumnNumber(1) + ".");
						}
					}
					else{
						if(isStartOfProperty){	//Properties outside the processes must have quantification defined for that process
							if(listOfAllProcessIDs.get(pNameorSet) != null)
							{
								if(!currentProcessName.equals(pNameorSet))
								{
									handleError(7, "Syntax Error: Invalid/Out of scope process name \"" + pNameorSet + "\" used at " + node.getLineAndColumnNumber(1));
								}
								pNameorSet = handleProcessNameForQuantification(node, boundVariable, boundVariables, pNameorSet);
							}
							else if(listOfAllProcessIDs.get(pNameorSet) == null)
							{
								handleError(7, "Syntax Error: Invalid/Out of scope process name \"" + pNameorSet + "\" used at " + node.getLineAndColumnNumber(1));
							}
							isStartOfProperty = false;
						}
						else if(pNameorSet.contains("."))//Child processes are refered using a dot with the bound variable of their parent process
						{
							pNameorSet = handleExtendedProcessNameForQuantification(boundNode, boundVariable, boundVariables, pNameorSet);
						}
						else
						{	//Add warning that the process refered in the second quantification is incorrect
							handleError(7, "Syntax Error: The process name is incorrect/incorrectly refered in the property at " + node.getLineAndColumnNumber(1) + ".");
//							listOfWarnings += "Error: Variable \"" + qVarName + "\" is not defined as a bound variable used at " + node.getLineAndColumnNumber(1) + ".\r\n";
						}
					}

					exp += " " + operator_in + " " + pNameorSet;
				}
				else
				{
					if(listOfAllProcessIDs.get(pNameorSet) != null)
					{
		                exp += " " + operator_in + " " + listOfAllProcessIDs.get(pNameorSet);
					}
					else
					{
		                exp += " " + operator_in + " " + pNameorSet;
					}
				}

					
               // exp += handleExpression(boundNode.jjtGetChild(i));
            }
            exp += " : ";
			String tmp = handleExpression(node.jjtGetChild(1));
			if(isExpressionForProperty)
			{
				if(tmp.startsWith("(") && !tmp.startsWith("\\A") && !tmp.startsWith("\\E"))
				{
					if(conditionStringForProperty.length() > 3) 
					{
						conditionStringForProperty = conditionStringForProperty.substring(0, conditionStringForProperty.length()-4);
						conditionStringForProperty += ") => ";
					}
					exp += conditionStringForProperty;
				}
				conditionStringForProperty = "";
				listOfQuantVars.clear();				
			}
            exp += tmp;
			
			

            symTab.removeAuxVariable(boundVariable);
            
			return exp;
		
	}
    
    /**
     * It handles the sub tree representing an expression.
     * @param node
     * @return      It returns the corresponding expression.
     */
    private String handleExpression(Node node)
    {
        int numChildren = node.jjtGetNumChildren();
        String nodeName = node.toString();
        String firstToken = node.getTextAt(0);
        String exp = "";	
		
		if(nodeName.equals("caseExpression"))
		{
            int numCaseArms = node.jjtGetNumChildren();
			exp = "CASE ";
            for(int i=0;i<numCaseArms;i++)
            {
				Node caseArmNode = node.jjtGetChild(i);
				if(caseArmNode.jjtGetNumChildren() == 2)
				{
	                Node condExpression = caseArmNode.jjtGetChild(0);
	                Node afterArrowExpression = caseArmNode.jjtGetChild(1);
				
					if(i != 0)
						exp += " [] ";
				
					exp += handleExpression(condExpression) + " -> " + handleExpression(afterArrowExpression);
				}
				else
				{
	                Node afterArrowExpression = caseArmNode.jjtGetChild(0);
				
					if(i != 0)
						exp += " [] ";
				
					exp += " OTHER -> " + handleExpression(afterArrowExpression);
				}
            }
			
		}
        else if(nodeName.equals("condExpression"))
        {
            Node condExp = node;
            exp = "IF " + handleExpression(condExp.jjtGetChild(0).jjtGetChild(0)) + " THEN " + handleExpression(condExp.jjtGetChild(1).jjtGetChild(0)) + " ELSE " + handleExpression(condExp.jjtGetChild(2).jjtGetChild(0));
        }
        else if(nodeName.equals("tupleExpression"))
        {
            exp = handleTupleExpression(node);
        }
        else if(nodeName.equals("functExpression"))
        {
        	exp = handleFunctExpression(node);
        }
        else if(nodeName.equals("quantExpression"))
        {
			exp = handleQuantificationExpression(node);
        }
        else if(nodeName.equals("setExpression"))
        {           
        	if(node.jjtGetNumChildren() > 0){  
        		Node expNode = node.jjtGetChild(0);
        		int k=0;
        		String he = handleExpression(expNode);
        		        		
        		exp = "{"; 
        		
        		if(node.jjtGetNumChildren() > 1)
        		{
        			String[] splitExp = {};
        			try{
        			exp += he.substring(0, he.length());
        			} catch (StringIndexOutOfBoundsException e){
        				exp += he;
        			}
        			
        			if(he.contains("\\in")){  
        				int aux = he.indexOf("\\in");            			
            			String var = he.substring(1, aux-1).trim();
                		String set = he.substring(aux+3,he.length()-1).trim();                		
                		knownWords.add(var);
                		
                		if(!knownWords.contains(set)){
                			symTab.checkDeclaration(set, "variable", 0, node.getLineAndColumnNumber(1));        				
                    	}
            		}        			
        			Node enumCompNode = node.jjtGetChild(1);
        			String name = enumCompNode.toString();
        			
        			if(name.equals("setComprehension"))
        			{
        				String heaux = handleExpression(enumCompNode.jjtGetChild(k));
        				if(heaux.contains("\\in")) {
        					if(splitExp.length == 0)
        						splitExp = he.split(" ");        					
        					
        					int aux = heaux.indexOf("\\in");            			
        					Boolean b = false;
        					
        					String var = heaux.substring(1, aux-1).trim();
        					String set = heaux.substring(aux+3,heaux.length()-1).trim();
        					
        					for(int j = 0; j < splitExp.length; j++){
        						b = b || (splitExp[j].equals(var) || splitExp[j].equals("("+var));
        						if(b)
        							break;
        					}
        					if(!b)
        						symTab.checkDeclaration(var, "variable", 0, node.getLineAndColumnNumber(1));
        					
        					if(!knownWords.contains(set) && !set.contains("..")){
        						symTab.checkDeclaration(set, "variable", 0, node.getLineAndColumnNumber(1));        				
                            }        					                    		
        				}        				        				
        				
        				exp += ":" + heaux.substring(1, heaux.length()-1);
        				k ++;
        			}
        			for(;k< enumCompNode.jjtGetNumChildren();k++)
        			{
        				expNode = enumCompNode.jjtGetChild(k);
        				exp += ", " + handleExpression(expNode);
        			}
        		}
        		else
        			exp += he;
        		exp += "}";
        	}else{
        		exp += "{}";        		
        	}
        }
        else if(nodeName.equals("infixOperator") && ( firstToken.equals("[") || firstToken.equals(".")))
        {
            if(firstToken.equals("["))
            {
                //e.g. network[father], network[p].know_winner(will have 2 selectors),..
                exp = generateNewSymbol(node.jjtGetChild(0).toString());
				exp = checkVariableAssignment(exp);		//Check if the variable was updated in the previous statements
				if(exp.equals("undeclaredvariable"))
				{
					//handleError(3, node.getLineAndColumnNumber(1));
				}
				
                int numSelectorNodes = node.jjtGetNumChildren();
                for(int i=1;i<numSelectorNodes;i++)
                {
                    exp += handleExpression(node.jjtGetChild(i));
                }
            }
            else
            {
                exp = generateNewSymbol(node.jjtGetChild(0).toString());
				exp = checkVariableAssignment(exp);		//Check if the variable was updated in the previous statements
                int numSelectorNodes = node.jjtGetNumChildren();
                for(int i=1;i<numSelectorNodes;i++)
                {
                    exp += handleExpression(node.jjtGetChild(i));
                }
            }
        }
        else if(nodeName.equals("letExpression")) // LET-IN construct
        {
        	Node funcOprDefNode = null;
        	Node expNode = node.jjtGetChild(node.jjtGetNumChildren()-1);
        	
        	int numchild = node.jjtGetNumChildren();
        	int i=0;
        	exp = "\n LET ";
        	for(i=0;i<numchild-1;i++)
        	{
        		if(i > 0)
        		{
        			exp += "     ";
        		}
        		funcOprDefNode = node.jjtGetChild(i);
        		if((funcOprDefNode.toString()).equals("operatorDefinition"))
        		{
        			exp += handleOperatorDefinition(funcOprDefNode) + "\n";
        		}
        		else
        		{
        			
        		}
        	}
        	exp += " IN ";
        	exp += handleExpression(expNode);
        	
        	
   
        }
		/*
			MUST be retested!
			*/
        else if(nodeName.compareTo("selector") == 0)
        {
			if(firstToken.equals("["))
			{
				exp = "[";
				int numChildNodes = node.jjtGetNumChildren();
				for(int i=0; i<numChildNodes; i++)
				{
				    exp += handleExpression(node.jjtGetChild(i));
					if(i<numChildNodes-1)
						exp += ", ";
				}
				exp += "]";
			}
			else
			{	
				exp = node.reproduceText();	//SA: Need further changes
			}
        }
        else if(numChildren >= 2)
        {     
            if(nodeName.compareTo("setExpression") == 0)
            {
                exp = node.reproduceText();
            }
            /*else if(nodeName.equals("letExpression")) moved.
            else if(nodeName.equals("letExpression"))
            {            	
            	String spaces = "     ";            	            	            	           
            	String beginSpaces = " ";
            	
            	if(node.jjtGetParent().jjtGetParent().jjtGetParent().jjtGetParent().toString().equals("process"))
            		exp = exp + "LET " + handleExpression(node.jjtGetChild(0)).substring(0, handleExpression(node.jjtGetChild(0)).length()-1) + " IN";
            	else
            		exp = exp + "\n" + beginSpaces + "LET " + handleExpression(node.jjtGetChild(0)).substring(0, handleExpression(node.jjtGetChild(0)).length()-1) + " IN";            		
            	
            	beginSpaces = beginSpaces  + " ";        			
            	
            	for(int i=1;i<numChildren;i++)
            	{   String aux = new String();
            		aux = handleExpression(node.jjtGetChild(i));
            		
            		if(symTab.checkDeclaration(node.jjtGetChild(i).getTextAt(1), "variable", 0, node.getLineAndColumnNumber(1)).equals("") 
            		&& node.jjtGetChild(i).toString().equals("operatorDefinition")){            			
            			exp = exp + "\n" + beginSpaces + "LET " + aux.substring(0, aux.length()-1) + " IN";
            			beginSpaces = beginSpaces  + " ";
            			spaces = spaces + " ";
            		}            			         		
            		else
            			exp = exp + "\n" + spaces + aux;              		
            	}    
            }*/
            else
            {  
            	String strOperator = node.reproduceOperator();            	
            	if(!nodeName.equals("functExpression")){
                	for(int j=1;j<numChildren;j++)
                		exp = exp + "(";                		
            		handDef = false;}
            	else{            		
            		exp = exp + strOperator;
            	}                                           
                if(strOperator.equals("@"))
            	{
            		String charFirst = node.jjtGetChild(0).getTextAt(1);
            		if(charFirst.equals("["))
            		{
            			String text = handleExpression(node.jjtGetChild(0));
            			String textRange = text.substring(0, text.indexOf("["));
            			String textIndex = text.substring(text.indexOf("[")+1,  text.length()-1);
            			exp += "_pc[lowerbound(" + textRange + ") + " + textIndex + " - 1] = \"" + node.jjtGetChild(1).reproduceText() + "\"";
            		}
            		else
            		{
            			String text = handleExpression(node.jjtGetChild(0));
            			exp += "_pc[" + text + "] = \"" + node.jjtGetChild(1).reproduceText() + "\"";
            		}
            		exp += ")";
            	}
            	else
            	{                
                if(node.jjtGetChild(0).toString().equals("nonfixLHS")){
                	
                	exp = exp.substring(1, exp.length()) + handleExpression(node.jjtGetChild(0))  + " == ";                	                 	
                	for(int i=1;i<numChildren;i++)
                	{   
                		exp = exp + handleExpression(node.jjtGetChild(i));	              		
                	}
                	exp = exp + "\n";                	
                }
                else{
                	exp = exp + handleExpression(node.jjtGetChild(0));
                	
                	for(int i=1;i<numChildren;i++)
                	{
                		if(!strOperator.equals("["))
	              			exp = exp + " " + strOperator + " ";
                		
	              		if(i == (numChildren-1) && handDef)
	              			exp = exp + handleExpression(node.jjtGetChild(i));
	              		else
	              			exp = exp + handleExpression(node.jjtGetChild(i)) + ")";
	              		
                	}
                }
            }
               
            }
        }
        else if(numChildren == 1)
        {  
            if(nodeName.compareTo("expression") == 0)
            {
                exp = handleExpression(node.jjtGetChild(0));  
            }
            else if(nodeName.compareTo("leftOperand") == 0)
            {
                String leftOperandChildName = node.jjtGetChild(0).toString();
                if(leftOperandChildName.equals("condExpression"))
                {
                    Node condExp = node.jjtGetChild(0);
                    exp = "IF " + handleExpression(condExp.jjtGetChild(0).jjtGetChild(0)) + " THEN " + handleExpression(condExp.jjtGetChild(1).jjtGetChild(0)) + " ELSE " + handleExpression(condExp.jjtGetChild(2).jjtGetChild(0));
                }
                else if(leftOperandChildName.equals("functExpression"))
                {
                    Node funcExp = node.jjtGetChild(0).jjtGetChild(0);
                    String funcExpName = node.jjtGetChild(0).jjtGetChild(0).toString();
                    if(funcExpName.equals("functConstruction"))
                    {
                        exp = "[" + funcExp.reproduceText() + "]";
                    }
                    else if(funcExpName.equals("recordConstruction"))
                    {
                        int recNum = funcExp.jjtGetNumChildren();
                        exp = "[";
                        for(int i=0;i<recNum;i++)
                        {
                            Node recChild = funcExp.jjtGetChild(i);
                            exp += recChild.getTextAt(1) + " " + recChild.getTextAt(2) + " "+ handleExpression(recChild.jjtGetChild(0).jjtGetChild(0));
                            if(i<recNum-1)
                                exp += ", ";
                        }
                        exp += "]";
                    }
                    else
                    {
                        exp = funcExp.reproduceText();
                    }
                    
                }
                else
                    exp = node.reproduceText();
            }
            else if(nodeName.compareTo("letExpression") == 0)
            {
                exp = node.reproduceText();
            }
            else if(nodeName.compareTo("tupleExpression") == 0)
            {
                exp = handleTupleExpression(node);
            }
            else if(nodeName.compareTo("sequenceExpression") == 0)
            {
                exp = handleSequenceExpression(node.jjtGetChild(0));
            }
            else if(nodeName.compareTo("functExpression") == 0)
            {
                exp = handleFunctExpression(node);
            }
			/*
            else if(nodeName.compareTo("selector") == 0)
            {
				System.out.println(node.reproduceText());
				exp = "[";
				int numChildNodes = node.jjtGetNumChildren();
				for(int i=0; i<numChildNodes; i++)
				{
				    exp += handleExpression(node.jjtGetChild(i));
				}
				exp += "]";
            }*/
            else
            {                
            	String n = node.jjtGetChild(0).toString();            	
            	if(n.compareTo("arguments") == 0)
                {
                    exp += nodeName + "(";
                    Node argumentsNode = node.jjtGetChild(0);                    
                    int noOfArguments = node.jjtGetChild(0).jjtGetNumChildren();
                   
                    for(int i=0;i < noOfArguments; i++)
                    {	                    	
                        exp += handleExpression(argumentsNode.jjtGetChild(i));
                        if(i < noOfArguments-1)
                            exp += ", ";
                    }
                    exp += ")";
                    String str = symTab.checkDeclaration(nodeName, "definition", noOfArguments, node.getLineAndColumnNumber(1));
                    
                    if(knownWords.contains(nodeName))
                    {
                        String startExp = exp.substring(0, exp.indexOf("(")+1);
                        String endExp = exp.substring(exp.indexOf("(")+1, exp.length());
                        exp = startExp + "self," + endExp;
                    }
                }
                else
                {
                    String operatorType = node.toString();
                    if(operatorType.compareTo("prefixOperator") == 0)
                    {
                        exp = "(" + node.reproduceOperator() + " ";
                        exp = exp + handleExpression(node.jjtGetChild(0)) + ")";
                    }
                    else if(operatorType.compareTo("postfixOperator") == 0)
                    {
                        exp = "(" + handleExpression(node.jjtGetChild(0));
                        exp = exp + " " + node.reproduceOperator() + ")";
                    }
                }
            }
        }
        else if(numChildren == 0)
        {			
            if(nodeName.compareTo("stringConstant") == 0)
            {
                exp = "\"" + node.reproduceText() + "\"";
            }
            else if(nodeName.compareTo("selector") == 0)
            {
                String n = node.getTextAt(2);
				if(isExpressionForProperty)
				{
					if(!processNameForSelector.equals(""))
					{
						if(!symTab.confirmDeclaration(processNameForSelector, n))
						{
							handleError(7, "Error: Variable \"" + n + "\" is not defined in process " + processNameForSelector + " at " + node.getLineAndColumnNumber(1) + ".");
						}
						processNameForSelector = "";
					}
				}				
                exp = generateNewSymbol(n);
                
                if(!isNumber(exp))
                {
                    exp = checkVariableAssignment(exp);
                }
                String dot = node.getTextAt(1);
                if(dot.equals("."))
                {
                    exp = node.reproduceText();
                }
                else
                {
                    exp += handleExpression(((node.jjtGetChild(0)).jjtGetChild(0)).jjtGetChild(0));
                }
            }
            else if(nodeName.compareTo("tupleExpression") == 0)
            {
                exp = handleTupleExpression(node);
            }
            else if(nodeName.equals("_text"))
            {
                exp = "\"" + node.getTextAt(1) + "\"";
            }
            else if(nodeName.equals("_number"))
            {
                exp = node.getTextAt(1);
            }
            else if(nodeName.equals("_true") || nodeName.equals("_false") || nodeName.equals("_self"))
            {
                exp = node.getTextAt(1);
            }
            else if(nodeName.equals("_super"))
            {
				if(currentProcessName.equals(""))	// super not allowed at algorithm level
				{
					handleError(8, node.getLineNumber());
				}       
					
                String lpar = node.getTextAt(2);
                if(lpar.equals("("))				// if super is followed by a process name
                {
                    exp = generateParentID(node.getTextAt(3));
					if(exp.equals(""))
					{
						handleError(6, node.getLineNumber());
					}
                }
                else								// if only super keyword is used, then reference to current process's parent should be returned
                {
                    exp = "_" + currentProcessName + "_data[self].parentID";
                }         
            }
            else if(nodeName.equals("nonfixLHS"))
			{
            	String text1 = node.getTextAt(1); 
            	
            	symTab.addSymbol(text1, "variable", "");            	
            	exp = generateNewSymbol(text1);            	
            	
			}
			else if(isExpressionForProperty && listOfQuantVars.containsKey(firstToken))
			{
				/* This allows the bound variables to be translated as they are if they are not used to access local variables of the processes */
				exp = firstToken;
			}
            else
            {   
				if(isExpressionForProperty)
				{//The variable accessed in the property should be a global variable, details of A1 are in SymbolTable
					String var = node.getTextAt(1);
					if(!symTab.confirmDeclaration("A1", var))
					{
						handleError(7, "Error: Variable \"" + var + "\" is not defined as a global variable at " + node.getLineAndColumnNumber(1) + ".");
					}
                	exp = generateNewSymbol(var);
				}
				else
				{
					String text1 = node.getTextAt(1);
	                String text2 = "";                
	                /*  Commented 22/11/2010: bug in the algorithm helpHandleDefinition
	                if(handDef){                	                	
	                	text2 = helpHandleDefinition(node).substring(1);                	
	                	symTab.checkDeclaration(text1, "variable", 0, node.getLineAndColumnNumber(1));
	                	exp = generateNewSymbol(text2);                	
	                } 
	                else*/ {
	                	if(!text1.equals("@"))
	                	{
	                		symTab.checkDeclaration(text1, "variable", 0, node.getLineAndColumnNumber(1));                    
	                	}  
	                	exp = generateNewSymbol(text1);
	                }
				}
            }
        }        
        if(!isNumber(exp) && !exp.equals("@"))
            exp = checkVariableAssignment(exp);
        return exp;
    }

    private String handleOperatorDefinition(Node node)
    {
    	String exp = "";
    	int index = 0;
    	String spaces = "    ";
    	if(node.jjtGetNumChildren() > 1)
    	{
    		Node temp = node.jjtGetChild(0);
    		if((temp.toString()).equals("PREFIX") || (temp.toString()).equals("nonfixLHS"))
    		{
    			//to be implemented
    			String token = temp.getTextAt(1);
    			int i = 2;
    			exp += token + " ";
    			while(!token.equals("=="))
    			{
    				token = temp.getTextAt(i);
    				i++;
    				exp += token + " ";
    			}
    			
    		}
    		index = 1;
    	}
    	else
    	{
    		String DEQstr = "==";
    		String tokenstr = "";
    		int ind = 2;
    		exp = node.getTextAt(1);
    		while(!tokenstr.equals(DEQstr))
    		{
    			tokenstr = node.getTextAt(ind);
    			exp += tokenstr + " ";
    			ind++;
    		}
    	}
    	exp += handleExpression(node.jjtGetChild(index));
    	
    	return exp;
    }
    private String handleTupleExpression(Node node)
    {
        String exp = "<<";
        int numExp = node.jjtGetNumChildren();
        for(int i=0;i<numExp;i++)
        {
            exp += handleExpression(node.jjtGetChild(i));
        	if(i < numExp-1)
        	{
        		exp += ", ";
        	}            
        }
        exp += ">>";
        return exp;
    }
    
    private String handleFunctExpression(Node node)
    {						
        String exp = "";
        Node funcExp = node.jjtGetChild(0);
        int numChild = node.jjtGetNumChildren();
        String funcExpName = funcExp.toString();
        if(funcExpName.equals("functConstruction"))
        {
            Node boundsNode = funcExp.jjtGetChild(0);
            Node boundNode = null;
            Node expNode = funcExp.jjtGetChild(1);
            int numBounds = boundsNode.jjtGetNumChildren();
            exp = "[";
            for(int i = 0; i < numBounds; i++)
            {
            	if(i>0)
            	{
            		exp+=", ";
            	}
                boundNode = boundsNode.jjtGetChild(i);
                String text = "";
                int j = 0;
                while(!text.equals("\\in"))
                {
                    j++;
                    text = boundNode.getTextAt(j);
                    exp += text + " ";
                }
                exp += handleExpression(boundNode.jjtGetChild(0));
            }
            exp += " |-> " + handleExpression(expNode);
            exp += "]";
        }
        else if(funcExpName.equals("recordConstruction"))
        {
            int recNum = funcExp.jjtGetNumChildren();
            
            exp = "[";
            for(int i=0;i<recNum;i++)
            {
                Node recChild = funcExp.jjtGetChild(i);
                exp += recChild.getTextAt(1) + " " + recChild.getTextAt(2) + " "+ handleExpression(recChild.jjtGetChild(0));
                if(i<recNum-1)
                    exp += ", ";
            }
            exp += "]";
        }
        else if(numChild == 2) //SA: Implemented on 29/11/2010 for [f EXCEPT ![x,y] = @+z] 
        {
        	Node functExceptNode = node.jjtGetChild(1);
        	String functExceptNodeName = functExceptNode.toString();
        	if(functExceptNodeName.equals("functExcept"))
        	{
                exp = "[";
                exp += handleExpression(funcExp) + " EXCEPT ![";
                
                Node overrideNode = functExceptNode.jjtGetChild(0);
                Node exp1Node, exp2Node;
                exp1Node = overrideNode.jjtGetChild(0);
                exp2Node = overrideNode.jjtGetChild(overrideNode.jjtGetNumChildren()-1);
                
                exp += handleExpression(exp1Node);
                
                if(overrideNode.jjtGetNumChildren() > 2)
                {
                	int index = 1;
                	while(index < overrideNode.jjtGetNumChildren()-1)
                	{
                		Node tempNode = overrideNode.jjtGetChild(index);
                		exp += ", " + handleExpression(tempNode);
                		index++;
                	}
                }
                exp += "] = ";
                String rhsExp = handleExpression(exp2Node);

                exp += rhsExp;
                exp += "]";
        	}
        }
        else
        {
            exp = funcExp.reproduceText();
        }
        return exp;
    }
    
    private String handleSequenceExpression(Node node)
    {
        String seqName = node.getTextAt(1);
        Node seqChild = node;
        String exp = "";
        if(seqName.equals("Append"))
        {
            exp = "Append(" + handleExpression(seqChild.jjtGetChild(0).jjtGetChild(0)) + ", " + handleExpression(seqChild.jjtGetChild(1).jjtGetChild(0)) + ")";
        }
        else
        {
            exp = seqName + "(" + handleExpression(seqChild.jjtGetChild(0).jjtGetChild(0)) + ")";
        }
        return exp;
    }
    
    private boolean isNumber(String str)
    {
        try
        {
            Integer.parseInt(str);
        }
        catch(Exception e)
        {
            return false;
        }
        return true;
        
    }
    /**
     * It handles the sub tree representing a run statement for a process or thread.
     * @param node
     */
    private void handleRun(Node node)
    {
        String name = node.getTextAt(1);
        int numInstances = 0;
        if(node.jjtGetNumChildren() > 0)
        {
            numInstances = (node.jjtGetChild(0)).jjtGetNumChildren();
        }
        Map var_List; 
        var_List = symTab.getVarDeclarations(name,"process", numInstances);

        String scope[] = symTab.getScopeInformation(name, "process", numInstances);
        String lhs1, lhs2, lhs3, lhs4, rhs1, rhs2, rhs3, rhs4;
        lhs1 = lhs2 = lhs3 = lhs4 = rhs1 = rhs2 = rhs3 = rhs4 = "";
        String lhs11, lhs22, lhs33, lhs44;
        lhs11 = lhs22 = lhs33 = lhs44 ="";
        
        ArrayList list = null;
        if(node.jjtGetNumChildren() > 0)
        {
            list = handleParameterInstances(node.jjtGetChild(0));
        }

        int listCounter = 0;
        String vars = "Name|->\"" + name + "\"";
        Iterator iter = var_List.entrySet().iterator(); 
        for (iter = var_List.entrySet().iterator(); iter.hasNext();)
        { 
            Map.Entry entry = (Map.Entry)iter.next();
            String key = (String)entry.getKey();
            String value = "";
            if(list != null)
            {
                if(listCounter < list.size())
                    value = (String)list.get(listCounter);
                else
                    value = (String)entry.getValue();
            }
            else
                value = (String)entry.getValue();
            if(value.compareTo("") == 0)
                value = "\"\"";
            vars += ", " + key + "|->" + value;
            listCounter++;
        }
        
        /************************changed single count and pc for all******************/
        if(scope[1].compareTo("algorithm") == 0)
        {
            String id = generateLocalID();
            lhs1 = checkVariableAssignment("_processCount");
            lhs2 = checkVariableAssignment("_" + name + "_data");
            lhs3 = checkVariableAssignment("_pc");
            lhs4 = checkVariableAssignment("_" + name + "_IDSet");
            lhs11 = "_processCount";
            lhs22 = "_" + name + "_data";
            lhs33 = "_pc";
            lhs44 = "_" + name + "_IDSet";
            rhs1 = lhs1 + " + 1";
            rhs2 = "[" + id + " \\in _" + lhs4 + " |-> IF " + id + " = _" + lhs1 + " THEN [" + vars + "] ELSE " + lhs2 + "[" + id + "] ]";
            rhs4 = lhs4 + " \\union {_" + lhs1 + "}";
        }
        else //if(scope[1].compareTo("process") == 0)
        {
            String id = generateLocalID();
            lhs1 = checkVariableAssignment("_processCount");
            lhs2 = checkVariableAssignment("_" + scope[0] + "_" + name + "_data");
            lhs3 = checkVariableAssignment("_pc");
            lhs4 = checkVariableAssignment("_" + scope[0] + "_" + name + "_IDSet");
            lhs11 = "_processCount";
            lhs22 = "_" + scope[0] + "_" + name + "_data";
            lhs33 = "_pc";
            lhs44 = "_" + scope[0] + "_" + name + "_IDSet";
            rhs1 = lhs1 + " + 1";
            rhs2 = "[" + id + " \\in _" + lhs4 + " |-> IF " + id + " = _" + lhs1 + " THEN [" + vars + "] ELSE " + lhs2 + "[" + id + "] ]";
            rhs4 = lhs4 + " \\union {_" + lhs1 + "}";
        }
        rhs3 = symTab.getLabelInformation(name, "process", numInstances);
        rhs3 = "Append(" + lhs3 + ", \"" + rhs3 + "\")";
        explodedTree.addStatement(currentLabelName, "_"+lhs1, rhs1);
        explodedTree.addStatement(currentLabelName, "_"+lhs4, rhs4);
        explodedTree.addStatement(currentLabelName, "_"+lhs2, rhs2);
        explodedTree.addStatement(currentLabelName, "_"+lhs3, rhs3);
        varList.put(lhs11, "_"+lhs1);
        varList.put(lhs22, "_"+lhs2);
        //varList.put(lhs3, "_"+lhs3);
        varList.put(lhs44, "_"+lhs4);
        wasLastStatementCallReturnGoto = true;
    }
    /*
     * Created by SA on 26/11/2010
     * */
    private void handleProcedureDefinitionCall(Node node)
    {
        String name = node.getTextAt(1);
        int numInstances = (node.jjtGetChild(0)).jjtGetNumChildren();
        String orgType = symTab.checkDeclaration(name, "procedure", numInstances, node.getLineAndColumnNumber(1));
        if(orgType.equals("procedure"))
        {
        	handleProcedureCall(node);
        }
        else
        {
        	handleDefinitionCall(node);
        }
		
		dontAddUpdation = false;	//If last statement of a process or main algorithm is a procedure call, then its updation statement must be added at the end
        
    }
    private void handleDefinitionCall(Node node)
    {
    	String name = node.getTextAt(1);
        String stmt;
        stmt = name;
        ArrayList<String> list =  handleParameterInstances(node.jjtGetChild(0));
        stmt += "(";
        for(int i=0;i<list.size();i++)
        {
        	stmt += list.get(i);
        	if(i < list.size()-1)
        	{
        		stmt += ", ";
        	}
        }
        stmt += ")";
        
        explodedTree.addStatement(currentLabelName, "", stmt);
    }
    /**
     * It handles the sub tree representing a procedure call statement for procedure.
     * @param node
     */
    private void handleProcedureCall(Node node)
    {
        String name = node.getTextAt(1);
        int numInstances = (node.jjtGetChild(0)).jjtGetNumChildren();
//        String orgType = symTab.checkDeclaration(name, "procedure", numInstances, node.getLineAndColumnNumber(1));
        Map var_List; 
        var_List = symTab.getVarDeclarations(name, "procedure", numInstances);
        if(var_List != null)
        {
            String scope[] = symTab.getScopeInformation(name, "procedure", numInstances);
            String lhs1, rhs1, rhs2;
            lhs1 = rhs1 = rhs2 = "";

            ArrayList list = handleParameterInstances(node.jjtGetChild(0));
            int listCounter = 0;
            String vars = "";
            Iterator iter = var_List.entrySet().iterator(); 
            for (iter = var_List.entrySet().iterator(); iter.hasNext();)
            { 
                Map.Entry entry = (Map.Entry)iter.next();
                String key = (String)entry.getKey();
                String value = "";
                if(listCounter < list.size())
                    value = (String)list.get(listCounter);
                else
                    value = (String)entry.getValue();
                if(value.compareTo("") == 0)
                    value = "\"\"";
                vars += key + "|->" + value + ", ";
                listCounter++;
            }

            vars += "_pc |->";
            
            lhs1 = "__stack";

            rhs1 = "[_stack EXCEPT ![self] = Push(_stack[self], <<[" + vars;
            rhs2 = symTab.getLabelInformation(name, "procedure", numInstances);
            //rhs2 = "[_pc EXCEPT ![self] = \"" + rhs2 + "\"]";
            addAssignedVariableToVarList("_stack");
            explodedTree.addStatement(currentLabelName, lhs1, rhs1);
            explodedTree.addUpdations(currentLabelName, "_pc", getRHSWithExcept("_pc[self]", "\""+rhs2+"\""));
            explodedTree.setPCID(currentLabelName, createPCID());
            wasLastStatementCallReturnGoto = true;
            isWithinBranch = false;
            wasLastStatementProcedureCall = true;
        }
    }
    /**
     * It handles parameter instances of all the method calls.
     * @param node
     * @return      It returns the list of value for parameters.
     */
    private ArrayList<String> handleParameterInstances(Node node)
    {
        
        ArrayList<String> list = new ArrayList<String>();
        for(int i=0; i<node.jjtGetNumChildren(); i++)
        {
            Node child = node.jjtGetChild(i);
            String exp = handleExpression((child.jjtGetChild(0)).jjtGetChild(0));
            list.add(exp);
        }
        return list;
    }
    private void handleAtomic(Node node)
    {
        Node child = node.jjtGetChild(0);
        String text = child.toString();
        String pre_currentLabelOfAtomicBlock = "";
		if(currentLabelOfAtomicBlock.equals(""))
		{
			currentLabelOfAtomicBlock = currentLabelName;
		}
		else
		{
			pre_currentLabelOfAtomicBlock = currentLabelOfAtomicBlock;
			currentLabelOfAtomicBlock = currentLabelName;
		}
        
        haveToAcquireLock = true;
        atomicBlockIsActive = true;
        if(text.equals("statements"))
        {
            handleBlock(child, "atomic");
        }
        //release atomic lock
        atomicBlockIsActive = false;
        if(!currentLabelName.equals(currentLabelOfAtomicBlock) && !wasSimpleLoopStatement)
        {
            if(!currentMethodType.equals("process"))
            {
                //explodedTree.addUpdations(currentLabelName, "cp", "IF depth - 1 = 0 THEN any ELSE self");
                varList.put("cp", "IF depth - 1 = 0 THEN any ELSE self");
            }
            else
            {
                //explodedTree.addUpdations(currentLabelName, "cp", "any");
                if(!wasLastStatementProcedureCall)
                    varList.put("cp", "any");
            }
            //explodedTree.addUpdations(currentLabelName, "depth", "depth - 1");
            varList.put("depth", "depth - 1");
        }
        wasLastStatementCallReturnGoto = false;
        branchContainedCallReturnGotoLabel = false;
        mustGenerateLabel = true;
		currentLabelOfAtomicBlock = pre_currentLabelOfAtomicBlock;
 	   //If the last statement inside the atomic statement was a branch or for then the updation statements would definitely be there
 	   //otherwise they must be added
 	   if(wasLastBranch || wasForLoopStatement)
	   {
 		   dontAddUpdation = true;		
		   wasForLoopStatement = false;
	   }
    }
	
    /**
     * This function generates a reference to parent's ID.
     * @param symbol It is the name of a process specified with the keyword "super" as "super(<Process Name>)"
	 * @return reference for the parent's ID
     */
    private String generateParentID(String symbol)
    {
        String scope[] = symTab.getScopeInformation(symbol, "variable", 0);
        String newSymbol = "";
		// if the name of the process specified in super(<Process name>) is confirmed and is not the current process
		if(!symbol.equals(currentProcessName) && scope[2].equals("ProcessID"))	
        {
            newSymbol = "";
            String pName = currentProcessName;
			String parentName = "";
            newSymbol = "_" + pName + "_data[self].parentID";
            while(true)	
            {
				parentName = symTab.getParentName(pName);
				if(!parentName.equals(symbol) && !parentName.equals(""))
				{
	                newSymbol = checkVariableAssignment(newSymbol);
	                newSymbol = "_" + parentName + "_data[" + newSymbol + "].parentID";
					pName = parentName;
				}	
				else
					break;		
            }
        }
		// if the name of the process specified in super(<Process name>) is not found as a process name then return "" 
        return newSymbol;
      }
    /**
     * The purpose of this function is to change the name of a variable according to its context for TLA+ translation.
		for example: if we have a variable "reqCS" declared inside a process "Peer". Then, it is changed from reqCS t
		o _Peer_data[self].reqCS or depending on the context.
     * @param symbol
     * @return      It returns the new symbol.
     */
    private String generateNewSymbol(String symbol)
    {
		
		//The iteration variable for with statement is always a local variable and is never declared globally.
        if(currentAuxVariables.size() > 0)
		{
			//To be deleted once tested
			//if(isWithinWithBlock && symbol.equals(currentAuxVariables.get(currentAuxVariables.size()-1)))
			if(isWithinWithBlock && currentAuxVariables.contains(symbol))
			{
				return symbol;		//Retruns without changing the name		
			}
		}
		String scope[] = symTab.getScopeInformation(symbol, "variable", 0);
		
        String newSymbol = "";
        if(scope[1].equals("NotDeclaredProcessName")) //FIX: change this miss leading string value. It refers to  if the process's name was found in the process's list 
        {
			if(isExpressionForProperty)
				newSymbol = "_" + symbol + "_data";
			else
            	newSymbol = symbol;//"_" + symbol + "_range";
        }
        else if(scope[1].compareTo("process") == 0)
        {
            String s = "";
            if(!currentProcessName.equals(scope[0]))
            {
                String pName = "";
                s = "_" + currentProcessName + "_data[self].parentID";
                pName = currentProcessName;
                while(true)
                {
                    s = checkVariableAssignment(s);
                    try{
                    pName = pName.substring(0, pName.lastIndexOf("_"));
                    } catch (Exception e) {                    	
                    	break;
                    }
                    if(pName.equals(scope[0]))
                        break;
                    s = "_" + pName + "_data[" + s + "].parentID";
                }
                newSymbol = "_" + scope[0] + "_data[" + s + "]." + symbol;
            }
            else
            {
//            	newSymbol = "_" + scope[0] + "_data";
  //          	newSymbol = checkVariableAssignment(newSymbol) + "[self]." + symbol;

            	newSymbol = "_" + scope[0] + "_data[self]." + symbol;
            }
			
        }
        else if(scope[2].equals("ProcessID"))
        {
            //newSymbol = "_" + scope[0] + "_range";
        //	newSymbol = scope[0];
			if(isExpressionForProperty)
			{
            	newSymbol = "_" + scope[0] + "_data";
			}
			else if(symbol.equals(scope[0]))
				{
					/*This must be redefined because if the current process is nested at a level more 1, then it would have to recalculate the parent's ID, e.g.,
						algorithm...
						network = [to \in A |-> <<>>]
						process A
							process B
								process C
									network[A] := ...		//Must be translated as network[_B_data[_C_data[self].parentID].parentID] := ....
							For the moment I am assuming that its directly above the current process	
						*/
						if(symbol.equals("super"))
							newSymbol = "_" + currentProcessName + "_data[self].parentID";
						else
							newSymbol = symbol;
						
					
			}
			else// To be tested
			{
				newSymbol = "UNDEFINED";
			}
			
/*
            String s = "";
            if(!currentProcessName.equals(scope[0]))
            {
                String pName = "";
                s = "_" + currentProcessName + "_data[self].parentID";
                pName = currentProcessName;
                while(true)
                {
                    s = checkVariableAssignment(s);
                    pName = pName.substring(0, pName.lastIndexOf("_"));

                    if(pName.equals(scope[0]))
                        break;
                    s = "_" + pName + "_data[" + s + "].parentID";
                }
                newSymbol = s;
                //System.out.println("here" + s);
            }
            else
            {
                newSymbol = currentProcessName;//"_" + currentProcessName + "_range";
            }*/
        }
        else if(scope[1].compareTo("function") == 0)
        {
            newSymbol = "Head(" + checkVariableAssignment("_stack") + "[self])." + symbol;
            /*
            if(scope[0].compareTo("") == 0)
            {
                newSymbol = "Head(_stack)." + symbol;
            }
            else
            {
                newSymbol = "Head(_" + scope[0] + "_stack[self])." + symbol;
            }*/
        }
        else if(scope[1].equals("auxillaryVariable"))
        {
			if(isExpressionForProperty)
				/*
					variables accessed inside a property are written like \A s \in S1 : \A c \in s.C2 : <>(s.s1a > c.c2a) 
					s1a is the local variable of process S1 and is accessed as s.s1a where s is the quantification variable.
					It represents the original process. This code below changes s to _S1_data[s] as in TLA+ code it will be 
					accessed in this way.
					*/
			{
				if(listOfQuantVars.get(symbol) != null)
				{
	        		newSymbol = "_" + listOfQuantVars.get(symbol) + "_data[" + symbol + "]";
					processNameForSelector = listOfQuantVars.get(symbol);
				}
				else
				{
	        		newSymbol = symbol;
				}
			}
			else
			{
	        	newSymbol = symbol;
			}
        }
        else
        {
			/* SA: Must be rewritten */
			if(isExpressionForProperty)
			{
	            scope = symTab.getScopeInformation(symbol, "variable", 0);
			}
			else
			{
	            scope = symTab.getScopeInformation(symbol, "definition", 0);
			}
            if(!scope[0].equals(""))
            {
                symbol = symbol + "(self)";
            }
            else
            {
					//return "undeclaredvariable";
            }
            newSymbol = symbol;
        }
		
        return newSymbol;
    }
    /**
     * It generates a local identifier for the scope of a label.
     * @return  It returns new ID.
     */
    private String generateLocalID()
    {
        String id = "id";
        String newID = "id";
        if(globalVarList.containsKey(newID))
        {
            int num = 1;
            newID = id + num;
            while(globalVarList.containsKey(newID))
            {
                num++;
                newID = id + num;
            }
        }
        return newID;
    }
    private String generateNewLabelAndAddToList(String location)
    {
        boolean notFound = true;
        String newlabel = "";
        while(notFound)
        {
            highestLabelNumber++;
            newlabel = "Lbl_" + highestLabelNumber;
            if(!labelList.containsKey(newlabel) && !listOfLabelsAfterLoops.contains(newlabel))
            {
                notFound = false;
            }
        }
        listOfLabelsAfterLoops.add(location+":"+newlabel);
		listOfWarnings += "Warning: New label \"" + newlabel + "\" generated at " + location + ".\r\n";
        //System.out.println("Warning: New label \"" + newlabel + "\" generated at " + location + ".");
		
        return newlabel;
    }
    /**
     * It generates new label if required.
     * @return      It returns label string.
     */
    private String generateNewLabel(String location)
    {
        boolean notFound = true;
        String newlabel = "";
		boolean found = false;
		
		//Loop statements generate new labels for statements following them that are stored in the variable "listOfLabelsAfterLoops". 
		//Before generating a new label,this function checks in the list if label has already been created for that location.
        if(listOfLabelsAfterLoops.size() > 0)
        {
			for(int i=listOfLabelsAfterLoops.size()-1;i>=0;i--)
			{
				String lbl =  listOfLabelsAfterLoops.get(i);
				String loc = lbl.substring(0, lbl.indexOf(":"));
				if(location.equals(loc))
				{
					newlabel = lbl.substring(lbl.indexOf(":")+1 , lbl.length());
					listOfLabelsAfterLoops.remove(lbl);
					found = true;
				}
			}
        }
		//If not found in the "listOfLabelsAfterLoops" then it creates new label
		if(!found)
		{
	        while(notFound)
	        {
	            highestLabelNumber++;
	            newlabel = "Lbl_" + highestLabelNumber;
	            if(!labelList.containsKey(newlabel))
	            {
	                notFound = false;
	            }
	        }
		}
		
		
		//Whenever a new label is generated, the previous label must know about the next label to jump to. 
        if(isWithinBranch && !branchFinished && !wasLastStatementCallReturnGoto)
        {//If the label is generated within branch/if else statement all the last statement was not call, return or goto then it should add the updation statement for pc
            String rhs = "[_pc EXCEPT ![self] = \"" + newlabel + "\"]";
            explodedTree.addUpdations(currentLabelName, "_pc", rhs);
            isWithinBranch = false;
        }
        else if(!isWithinForLoop && !wasLastStatementCallReturnGoto)
        {
            explodedTree.setNextPC(currentLabelName, "\""+newlabel+"\"");
            explodedTree.setPCID(currentLabelName, createPCID());
        }
		else if(isWithinForLoop && !wasLastStatementCallReturnGoto)
        {
            String rhs = "[_pc EXCEPT ![self] = \"" + newlabel + "\"]";
            explodedTree.addUpdations(currentLabelName, "_pc", rhs);
            explodedTree.setNextPC(currentLabelName, "\""+newlabel+"\"");
            explodedTree.setPCID(currentLabelName, createPCID());
        }
		
        if(branchFinished)
        {
            explodedTree.setAllNextPC(currentLabelName, "\""+newlabel+"\"");
        }
        
        labelList.put(newlabel, newlabel);
		
        explodedTree.addAction(newlabel);
        
            if(currentMethodType.equals("procedure"))
            {
                explodedTree.addGuard(newlabel, "(cp = any \\/ cp = self)");
            }
            else
            {
                if(atomicBlockIsActive)
                {
                    explodedTree.addGuard(newlabel, "cp = self");
                }
                else
                {
                    explodedTree.addGuard(newlabel, "cp = any");
                }
            }
        String newlabelSelf = newlabel;
        //if(currentProcessName.compareTo("") != 0)
        {
            explodedTree.setHasSelf(newlabel);
            newlabelSelf = newlabel + "(self)";
        }
        if(localLabelList.compareTo("") == 0)
            localLabelList = newlabelSelf + " ";
        else
            localLabelList+= "\\/ " + newlabelSelf + " ";
		//processFinished : If its the first label of a process then the updation information must not be added to previous action
        if(currentLabelName.compareTo("") != 0 && !branchFinished && !processFinished)	
        {
 /*           if(haveToAcquireLock && atomicBlockIsActive)
            {
                //explodedTree.addUpdations(currentLabelName, "cp", "self");
                //explodedTree.addUpdations(currentLabelName, "depth", "depth + 1");
                varList.put("cp", "self");
                varList.put("depth", "depth + 1");
                haveToAcquireLock = false;
            }*/
		 	lastActionCompleted = true;
           	addUpdationInformation();
			lastActionCompleted = false;
        }
        else
            branchFinished = false;
        varList.clear();
        if(wasLastStatementProcedureCall)
        {
            if(wasLastLoopStatement)
            {
                explodedTree.setCallReturnPCID(currentLabelName, "\"" + currentLoopLabel + "\"");
				currentLoopLabel = "";
            }
            else if(branchFinished)
            {
                explodedTree.setCallReturnPCID(currentLabelName, "\">>>" + newlabel + "\"");
            }
            wasLastStatementProcedureCall = false;
            wasLastLoopStatement = false;
            //currentLoopLabel = "";
        }
		listOfWarnings += "Warning: New label \"" + newlabel + "\" generated at " + location + ".\r\n";
//        System.out.println("Warning: New label \"" + newlabel + "\" generated at " + location + ".");
		haveToAcquireLock = false;
		processFinished = false;
        return newlabel;
    }
    /**
     * It adds the label read from pcal algorithm but if it already exists in the list, then generates new one.
     * @param labelName
     * @return      It return label name.
     */
    private String addLabel(String labelName, String location)
    {
        String label = "";
		boolean check_isWithinBranch = false;
        boolean newLabelGenerated = false;
		//Creates new label if it already exists in the program.
        if(labelList.containsKey(labelName) || globalVarList.get(labelName) != null)
        {
            if(labelOfFirstAtomicStatementUsed)
            {
                labelOfFirstAtomicStatementUsed = false;
                return currentLabelName;
            }
            label = generateNewLabel(location);
            newLabelGenerated = true;
        }
        else//If it does exist in the program then it adds it in the list of labels and adds the pc updation statements according to different conditions.
        {
            
            if(listOfLabelsAfterLoops.contains(labelName))
            {
                listOfLabelsAfterLoops.remove(labelName);
            }
			
             label = labelName;
			
            //a statement to update pc with the new label must be added in the last label whenever a new label is created
			if(isWithinBranch && !branchFinished && !wasLastStatementCallReturnGoto)//If current label is inside branch and last statement was not goto then it adds it otherwise handle
            {
                String rhs = "[_pc EXCEPT ![self] = \"" + label + "\"]";
                explodedTree.addUpdations(currentLabelName, "_pc", rhs);
                isWithinBranch = false;
				check_isWithinBranch = true;
            }
            else if(!isWithinBranch && !wasLastLoopStatement)//If last statement was a loop statement then it must have already added it 
			{
				if(!wasLastStatementProcedureCall)
				{
	                explodedTree.setNextPC(currentLabelName, "\""+label+"\"");
	                explodedTree.setPCID(currentLabelName, createPCID());
				}
            }
			//Condition requries re-testing
			else if(!isWithinBranch) //In case of for loop the pcid statement was not correctly added
			{
//				System.out.println("ADDING label.........................." + currentLabelName + " : " + label + " : " + location );
                explodedTree.setNextPC(currentLabelName, "\""+label+"\"");
                explodedTree.setPCID(currentLabelName, createPCID());
            }
			
			//If last statement was a branch then it makes sure that all the arms have a value set of pc. 
            if(branchFinished)
            {
                explodedTree.setAllNextPC(currentLabelName, "\""+label+"\"");
            }
			//
            explodedTree.addAction(label);
           // explodedTree.setNextPC(label, "\"Done\"");
            
            if(currentMethodType.equals("procedure"))
            {
                explodedTree.addGuard(label, "(cp = any \\/ cp = self)");
            }
            else
            {
                if(atomicBlockIsActive)
                {
                    explodedTree.addGuard(label, "cp = self");
                }
                else
                {
                    explodedTree.addGuard(label, "cp = any");
                }
            }
            String newlabelSelf = label;
            //if(currentProcessName.compareTo("") != 0)
            {
                explodedTree.setHasSelf(label);
                newlabelSelf = label + "(self)";
            }
            if(localLabelList.compareTo("") == 0)
                localLabelList = newlabelSelf + " ";
            else
                localLabelList+= "\\/ " + newlabelSelf + " ";
        }
        if(!newLabelGenerated)
        {
			//processFinished : If its the first label of a process then the updation information must not be added to previous action
            if(!currentLabelName.equals("") && !branchFinished && !processFinished)
            {
/*                if(haveToAcquireLock && atomicBlockIsActive)
                {
                    //explodedTree.addUpdations(currentLabelName, "cp", "self");
                    //explodedTree.addUpdations(currentLabelName, "depth", "depth + 1");
                    varList.put("cp", "self");
                    varList.put("depth", "depth + 1");
                    haveToAcquireLock = false;
					System.out.println("Acquiring lock at label : " + currentLabelName);
                }*/
                lastActionCompleted = true;
				addUpdationInformation();
                lastActionCompleted = false;
            }
            else
                branchFinished = false;
            varList.clear();
            labelList.put(label, label);

            if(wasLastStatementProcedureCall)
            {
                if(wasLastLoopStatement)
                {
                    explodedTree.setCallReturnPCID(currentLabelName, "\"" + currentLoopLabel + "\"");
					currentLoopLabel = "";
                }
//                else if(!check_isWithinBranch)
				else if(branchFinished)
                {
                    explodedTree.setCallReturnPCID(currentLabelName, "\"" + label + "\"");
                }
				
				
                wasLastStatementProcedureCall = false;
                wasLastLoopStatement = false;
                //currentLoopLabel = "";
            }
        }
		haveToAcquireLock = false;
		wasLastLoopStatement = false;
		processFinished = false;			//Once a new label has been created this means that a new process has started
        return label;
    }

    /**
     * It adds the information regarding variables at the end of the label.
     */
    private void addUpdationInformation()
    {
		if(haveToAcquireLock && atomicBlockIsActive)
        {
            //explodedTree.addUpdations(currentLabelName, "cp", "self");
            //explodedTree.addUpdations(currentLabelName, "depth", "depth + 1");
            varList.put("cp", "self");
            varList.put("depth", "depth + 1");
            //haveToAcquireLock = false;
        }
		else if(haveToReleaseLock && !lastActionCompleted) //!wasSimpleLoopStatement) // !wasSimpleLoopStatement is added because loop statement doesnt add its updation statement
			//the statement following the loop statement adds it and releaselock is not activated for loop in that case
		{
            varList.put("cp", "IF depth - 1 = 0 THEN any ELSE self");
            varList.put("depth", "depth - 1");
		}
        varList.remove("_newhead");
		//System.out.println("Current label name : " + currentLabelName + " current lable of atomic :" + currentLabelOfAtomicBlock);
        for (Map.Entry<String, String> entry: varList.entrySet()) {
            explodedTree.addUpdations(currentLabelName, entry.getKey(), entry.getValue());
        }
        calculateChangedVariables();
    }
    /**
     * It adds information regarding changed variables at the end of label.
     */
    private void calculateChangedVariables()
    {
        String list = "";
        for (String changedVar :  varList.keySet())
        {
            list += changedVar + " ";
        }
        explodedTree.addUpdations(currentLabelName, "UNCHANGED", list);
    }
    /**
     * It adds new variable to varList that contains the information about the changed variables.
     * @param var   It is the new variable to be added.
     * @return      It returns the new variable name for the old one.
     */
    private String addAssignedVariableToVarList(String var)
    {
        String sym = "";
        if(varList.containsKey(var))
            sym = (String)varList.get(var);
		
//		if(var.equals("_stack"))
//			System.out.println(">>>here we are : " + sym);
		
		
        if(sym.compareTo("") != 0)
        {
            if(sym.startsWith("Head("))
            {
                String symInitialPart = sym.substring(0, 5);
                String symLastPart = sym.substring(5);
                
                sym = symInitialPart + "_" + symLastPart; 
                
                //sym = sym.r("Head(","Head(_");
            }
            else
                sym = "_" + sym;
        }
        else
        {            
            if(var.startsWith("Head("))
            {    
                String symInitialPart = var.substring(0, 5);
                String symLastPart = var.substring(5);
                
                sym = symInitialPart + "_" + symLastPart; 
                //sym = var.replaceFirst("Head(","Head(_");
            }
            else
                sym = "_" + var;
        }
        varList.put(var, sym);

        return sym;
    }
    private void removeFromVarList(String symbol)
    {
        varList.remove(symbol);
    }
    /**
     * It checks whether the variable is already assigned a new value or not, which in other
     * words mean that the variable ID has changed or not.
     * @param var   It is the variable to be checked.
     * @return      It returns the latest ID for the variable.
     */
    private String checkVariableAssignment(String var)
    {
        String sym = "";
        if(varList.containsKey(var))
        {
            sym = (String)varList.get(var);
        }
        else if(var.contains("["))
        {
            String preText = var.substring(0, var.indexOf("["));
            String extension = var.substring(var.indexOf("["));
            if(varList.containsKey(preText))
            {
                sym = (String)varList.get(preText);
                sym += extension;
            }
			else if(var.startsWith("Head"))
			{
				preText = var.substring(var.indexOf("(")+1, var.indexOf("["));
				
				sym = findVariable(preText);
				sym = "Head(" + sym + extension;
			}
            else
            {
                sym = var;
            }
        }
        else
        {
            sym = var;
        }
        return sym;
    }
	/*
		This function finds the name of the variable in the "var" that is possibly
		"_stack" for the moment. It can be modified if required
		*/
	
	private String findVariable(String var)
	{
		String sym = "";
		
		if(var.endsWith("_stack"))//If the variable is "_stack" but contains _s 
		{
			while(!var.equals("_stack"))//removes _s making sure its the same _stack 
			{
				if(var.startsWith("_"))
					var = var.substring(1, var.length());
				else
					break;
				
			}
			sym = (String)varList.get(var);
		}
		else
			sym = var;

		if(sym == null)//sym will be null if its not found in the varList
			return var;
		else
			return sym;
	}
    /**
     * It handles the sub tree representing the temporal/invariant properties.
     * @param node
     */
    private void handleProperty(Node node, String methodName)
    {
        String childName = node.jjtGetChild(0).toString();
        Node childExpression = (node.jjtGetChild(0)).jjtGetChild(0);
        isExpressionForProperty = true;
		isStartOfProperty = true;
		isAlgorithmLevelProperty = true;
        String expression = handleExpression(childExpression.jjtGetChild(0));
		//System.out.println(expression);
		isAlgorithmLevelProperty = false;
		isStartOfProperty = false;
        isExpressionForProperty = false;
        /*
		if(!methodName.equals("Main"))
        {
            expression = "\\A self \\in " + listOfAllProcessIDs.get(methodName) + " : " + expression;
        }
			*/
        if(childName.compareTo("temporal") == 0)
        {
            explodedTree.addToPropertyList(expression,"temporal");
        }
        else
        {
            explodedTree.addToPropertyList(expression, "invariant");
        }
        
    }
    private void handlePropertySectionOutside(Node node)
    {
        String childName = node.jjtGetChild(0).toString();
        Node childExpression = (node.jjtGetChild(0)).jjtGetChild(0);
        isExpressionForProperty = true;
		isStartOfProperty = true;
		String expression = handleExpression(childExpression.jjtGetChild(0));
		isStartOfProperty = false;
        isExpressionForProperty = false;
        if(childName.compareTo("temporal") == 0)
        {
            explodedTree.addToPropertyList(expression,"temporal");
        }
        else
        {
            explodedTree.addToPropertyList(expression, "invariant");
        }
    }
    private void handleInstance(Node node)
    {
        int numChild = node.jjtGetNumChildren();
        for(int i = 0; i < numChild; i++)
        {
            Node childConfig = node.jjtGetChild(i);
            String childName = childConfig.jjtGetChild(0).toString();
            if(childName.equals("constantDefs"))
            {
                Node constantChild = childConfig.jjtGetChild(0);
                int numConstChild = constantChild.jjtGetNumChildren();
                for(int j=0;j<numConstChild;j++)
                {
                    Node child = constantChild.jjtGetChild(j);
                    String constantVar = child.getTextAt(1);
                    String expression = handleExpression((child.jjtGetChild(0)).jjtGetChild(0));
                    
                    if(expression.startsWith("["))
                    {
                        explodedTree.addConstantInitInfo(constantVar + " == " + expression, "tla");
                    }
                    else
                    {
                        explodedTree.addConstantInitInfo(constantVar + " = " + expression, "cfg");
                    }
                }
            }
            else if(childName.equals("constraint"))
            {
            	Node constraintChild = childConfig.jjtGetChild(0);
            	String expression = handleExpression(constraintChild.jjtGetChild(0));
            	explodedTree.addToConstraintList(expression);
            }
        }
    }
    
    private void handleError(int errorID, String msg)
    {
        switch(errorID)
        {
            case 1: System.out.println("Error: Invalid For/With Construct." + msg); break;
            case 2: System.out.println("Error: Statement after the Loop should be labeled."); break;
            case 3: System.out.println("Error at " + msg);break;
			case 4: System.out.println("Syntax Error: Invalid With statement." + msg);break;
			case 5: System.out.println("Syntax Error: Labels are not allowed inside With statement.");break;
			case 6: System.out.println("Syntax Error: Invalid process name used or out of scope at " + msg + ".");break;
			case 7: System.out.println(msg);break;
			case 8: System.out.println("Syntax Error: super not allowed at " + msg + ". It can only be used inside a process.");break;
			
        }
        
        System.exit(0);
    }
    
}
