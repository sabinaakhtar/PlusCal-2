
import java.util.*;
import java.util.Map.Entry;

interface ExplodedTreeInterface{
    public void setPCID(String label, String id);
    public void setCallReturnPCID(String label, String id);
    public void setNextPC(String lastLabel, String label);
    public void setHasSelf(String lastLabel);
    public void addToNextList(String next);
    public void setAllNextPC(String labelName, String nextPCLabel);
    public void addAction(String labelName);
    public void addStatement(String labelName, String lhs, String rhs);
    public void addGuard(String labelName, String guard);
    public void addDefinition(String definitionName, String exp, String parameters, int numParameters);
    public void addGlobalDefinition(String definitionName, String exp, String parameters, int numParameters);
    public void addUpdations(String labelName, String lhs, String rhs);
    public void addBranch(String labelName, boolean isBranch);
    public void addCase(String labelName, String cond, boolean isBranch);
    public void addElse(String labelName);
    public void addEnd(String labelName, boolean isbranch);
    public void addToFairList(String name, String fair);
    public void addToPropertyList(String property, String type);
    public void addToConstraintList(String constraint);
    public void addVariable(String name, String initialization);
    public void addConstantInitInfo(String constantInit, String file);
    public void setHeaderInformation(String info);
    public String getHeaderInformation();
    public String getVariableList();
    public String getLabelDescrption();
    public String getPropertyDescription();
    public int getNumOfProperties(String type);
    public String getFairnessDescription();
    public String createFairnessStatement(String key, String type);
    public String getConstantDefInfo();
    public void copyListOfAllProcessIDs(Map<String, String> list);
    public void addNoStatementProcess(String process);
    public void setMainActive();
    public void addRangeDefinition(String name, String value);
    public void insertAuxVariableInitializationStatement(String labelName, String variableName, String updationVar);
    public void updateStatement(String labelName, String lhs, String rhs);
}

public class ExplodedTree implements ExplodedTreeInterface{
    
    Map<String, ActionStructure> actions = new LinkedHashMap<String, ActionStructure>();
    String currentAction = "";
    Map<String, String> varList = new LinkedHashMap<String, String>();
    String headerInformation = "";
    ArrayList<String> nextList = new ArrayList<String>();
    Map<String, String> fairList = new LinkedHashMap<String, String>();
    ArrayList<String> invariantList = new ArrayList<String>();
    ArrayList<String> temporalList = new ArrayList<String>();
    ArrayList<String> constraintList = new ArrayList<String>();
    String constantInitForConfigFile = "";
    String constantInitForTLAFile = "";
    Map<String, String> listOfAllProcessIDs=null;
    ArrayList<String> noStatementProcess = new ArrayList<String>();
    boolean isMainActive = false;
    Map<String, String> processIDDefinitions = new LinkedHashMap<String, String>();
    ArrayList<String> listOfDefinitions = new ArrayList<String>();
    
    String oneTab = "    ";
    
    class ActionStructure {
        String nextPC = "";
        String pcID = "";
        boolean hasSelf = false;
        boolean isDefinition = false;
        boolean isForLoop = false;
        String callReturnPCID = "";
        Map<Object, Statement> statements = new LinkedHashMap<Object, Statement>();
    }
    
    class Statement{
        String typeName = "";
        String lHS = "", rHS = "";
        String condition = "";
        boolean isBranch = false;
        
        public void createStatement(String type, String lhs, String rhs){
            typeName = type;
            lHS = lhs;
            rHS = rhs;
        }
        public void createBranch(boolean isbranch){
            typeName = "branch";
            isBranch = isbranch;
        }
        public void createElse(){
            typeName = "else";
        }
        public void createCase(String cond, boolean isbranch){
            typeName = "case";
            condition = cond;
            isBranch = isbranch;
        }
        public void endBranch(boolean isbranch){
            typeName = "end";
			isBranch = isbranch;
        }
    }
    
    public void setIsForLoop(String label)
    {
        if(!label.equals("")) {
            ActionStructure as = (ActionStructure)actions.get(label);
            as.isForLoop = true;
        }
    }
    public void setMainActive()
    {
        isMainActive = true;
    }
    public void copyListOfAllProcessIDs(Map<String, String> list)
    {
        listOfAllProcessIDs = new LinkedHashMap<String, String>();
        listOfAllProcessIDs.putAll(list);
    }
    public void addNoStatementProcess(String process)
	{
		noStatementProcess.add(process);
	}
	
    
    public void setPCID(String label, String id)
    {
        if(!label.equals("")) {
        ActionStructure as = (ActionStructure)actions.get(label);
        if(as.pcID.equals(""))
            as.pcID = id;
        }
    }
    public void setCallReturnPCID(String label, String id)
    {
        if(!label.equals("")) {
        ActionStructure as = (ActionStructure)actions.get(label);
        if(as.callReturnPCID.equals(""))
            as.callReturnPCID = id;
//        System.out.println("setting to id:" + id + " at label : " + label);
		}
    }
    public void setNextPC(String lastLabel, String label){ 		
		if(!lastLabel.equals("")) {
        ActionStructure as = (ActionStructure)actions.get(lastLabel);
       if(as.nextPC.equals(""))
        {
            as.nextPC = label;
        }
		}
    }
    public void setHasSelf(String lastLabel)
    {
        if(!lastLabel.equals(""))
        {
            ActionStructure as = (ActionStructure)actions.get(lastLabel);
            as.hasSelf = true;
        }
    }
    public void addToNextList(String next)
    {
        nextList.add(next);
    }
    public void setAllNextPC(String labelName, String nextPCLabel)
    {
		//System.out.println("Must recheck the translation!!!!!!!!!!!!");
        boolean fillNextRecords = false;
        for (Map.Entry<String, ActionStructure> entry: actions.entrySet()) {
            String key = entry.getKey();
            ActionStructure value = entry.getValue();
            //Requires testing
			//this is condition is moved from **
            if(key.equals(labelName))
                fillNextRecords = true;
			
            if(fillNextRecords && value.nextPC.equals("") && !value.pcID.equals(""))
            {
                value.nextPC = nextPCLabel;
            }

			//This statement is added because ** was moved
			//fillNextRecords = false;
			
            
			//**
        }
    }
    public void addAction(String labelName){
        ActionStructure as = new ActionStructure();
        actions.put(labelName, as);
        currentAction = labelName;
    }
    public void addDefinition(String definitionName, String exp, String parameters, int numParameters){
    	ActionStructure as = (ActionStructure)actions.get(numParameters + "_" + definitionName);
        Statement s = new Statement();       
        s.createStatement("definition", exp, parameters);        
        (as.statements).put(1, s);
        as.isDefinition = true;               
    }
    public void addGlobalDefinition(String definitionName, String exp, String parameters, int numParameters){
    	listOfDefinitions.add(definitionName + parameters + " == " + exp);
    }
    public void addStatement(String labelName, String lhs, String rhs){
        ActionStructure as = (ActionStructure)actions.get(labelName);
        int statementNum = -1;
        try{
            statementNum = (as.statements).size() + 1;
        }
        catch(Exception e){
            throwExceptionAndExit(e);
        }
        Statement s = new Statement();
        s.createStatement("statement", lhs, rhs);
        (as.statements).put(statementNum, s);
    }
    public void updateStatement(String labelName, String lhs, String rhs){
        ActionStructure as = (ActionStructure)actions.get(labelName);
		
		int index = (as.statements).size()-1;
		
		for(int i=index;i>0;i--)
		{
			Statement value = (as.statements).get(i);
			if(value != null)
			{
	            if(value.lHS.equals(lhs))
				{
					value.rHS += rhs + "]>>)]";
					(as.statements).put(i, value);
					break;
				}
			}
		}
    }
    public void addAuxStatement(String labelName, String lhs, String rhs){
        ActionStructure as = (ActionStructure)actions.get(labelName);
        int statementNum = -1;
        try{
            statementNum = (as.statements).size() + 1;
        }
        catch(Exception e){
            throwExceptionAndExit(e);
        }
        Statement s = new Statement();
        s.createStatement("auxstatement", lhs, rhs);
        (as.statements).put(statementNum, s);
    }
    public void addGuard(String labelName, String guard){
        ActionStructure as = (ActionStructure)actions.get(labelName);
        int statementNum = -1;
        try{
            statementNum = (as.statements).size() + 1;
        }
        catch(Exception e){
            throwExceptionAndExit(e);
        }
        Statement s = new Statement();
        s.createStatement("guard", guard, "");
        (as.statements).put(statementNum, s);
    }
    public void addWithStatement(String labelName, String lhs, String rhs){
        ActionStructure as = (ActionStructure)actions.get(labelName);
        int statementNum = -1;
        try{
            statementNum = (as.statements).size() + 1;
        }
        catch(Exception e){
            throwExceptionAndExit(e);
        }
        Statement s = new Statement();
        s.createStatement("with", lhs, rhs);
        (as.statements).put(statementNum, s);
    }
    public void addUpdations(String labelName, String lhs, String rhs){
        ActionStructure as = (ActionStructure)actions.get(labelName);
        int statementNum = -1;
        try{
            statementNum = (as.statements).size() + 1;
        }
        catch(Exception e){
            throwExceptionAndExit(e);
        }
        Statement s = new Statement();
        s.createStatement("updation", lhs, rhs);
        (as.statements).put(statementNum, s);
    }
    public void addBranch(String labelName, boolean isBranch){
        ActionStructure as = (ActionStructure)actions.get(labelName);
        int statementNum = -1;
        try{
            statementNum = (as.statements).size() + 1;
        }
        catch(Exception e){
            throwExceptionAndExit(e);
        }
        Statement s = new Statement();
        s.createBranch(isBranch);
        (as.statements).put(statementNum, s);
    }
    public void addElse(String labelName){
        ActionStructure as = (ActionStructure)actions.get(labelName);
        int statementNum = -1;
        try{
            statementNum = (as.statements).size() + 1;
        }
        catch(Exception e){
            throwExceptionAndExit(e);
        }
        Statement s = new Statement();
        s.createElse();
        (as.statements).put(statementNum, s);
    }
    public void addCase(String labelName, String cond, boolean isBranch){
        ActionStructure as = (ActionStructure)actions.get(labelName);
        int statementNum = -1;
        try{
            statementNum = (as.statements).size() + 1;
        }
        catch(Exception e){
            throwExceptionAndExit(e);
        }
        Statement s = new Statement();
        s.createCase(cond, isBranch);
        (as.statements).put(statementNum, s);
    }
    public void addEnd(String labelName, boolean isbranch){
        ActionStructure as = (ActionStructure)actions.get(labelName);
        int statementNum = -1;
        try{
            statementNum = (as.statements).size() + 1;
        }
        catch(Exception e){
            throwExceptionAndExit(e);
        }
        Statement s = new Statement();
        s.endBranch(isbranch);
        (as.statements).put(statementNum, s);
    }
    public void addToFairList(String name, String fair)
    {
        fairList.put(name, fair);
    }
    public void addToPropertyList(String property, String type)
    {
        if(type.compareToIgnoreCase("temporal") == 0)
        {
            temporalList.add(property);
        }
        else
        {
            invariantList.add(property);
        }
    }
    public void addToConstraintList(String constraint)
    {
    	constraintList.add(constraint);
    }
    public void addVariable(String name, String initialization){
        if(name.equals("_pc"))
        {
            varList.remove(name);
            varList.put(name, initialization);
        }
        else
        {
            varList.put(name, initialization);
        }
    }
    public void addConstantInitInfo(String constantInit, String file)
    {
        if(file.equals("cfg"))
        {	
            constantInitForConfigFile += oneTab + constantInit + "\n";
        }
        else if(file.equals("tla"))
        {
            constantInitForTLAFile += constantInit + "\n";
        }
    }
    public void setHeaderInformation(String info)
    {
        headerInformation += info;
    }
    public String getHeaderInformation()
    {
        return headerInformation;
    }
    private void throwExceptionAndExit(Exception e){
        System.out.println("Exception occured: " + e.getMessage());
        System.exit(1);
    }
    public void insertAuxVariableInitializationStatement(String labelName, String lhs, String updationVar)
    { /* FIXME: kill this function? It has no return nor side effect */
        ActionStructure as = (ActionStructure)actions.get(labelName);
        Map<Object,Statement> temp_statments = new LinkedHashMap<Object,Statement>();
        for (Map.Entry<Object, Statement> entry: as.statements.entrySet()) {
            Statement key2 = (Statement)entry.getValue();
            if(key2.typeName.equals("updation"))
            {
                temp_statments.put(entry.getKey(), entry.getValue());
            }
            else
            {
                temp_statments.put(entry.getKey(), entry.getValue());
            }
        }


    }
    public String getVariableList()
    {
        String varlist = "VARIABLES";
        String list = "";
        for (String key : varList.keySet()) {
            
            if(key.startsWith("?")){
            	PcalTranslator.knownWords.add(key.substring(1, key.length()));
                list += " " + key.substring(1, key.length()) + ",";
            }
            else{
                list += " " + key + ",";
                PcalTranslator.knownWords.add(key);
            }
        }
        list = list.substring(0, list.length()-1);
        varlist+=list;
        varlist+="\n\nvars == <<" + list + " >>";        
        
        varlist += "\n\nupperbound(S) == CHOOSE n \\in S : \n" + oneTab + oneTab + oneTab + "/\\ \\A m \\in S : n >= m";
        varlist += "\n\nlowerbound(S) == CHOOSE n \\in S : \n" + oneTab + oneTab + oneTab + "/\\ \\A m \\in S : m >= n";
        
        for (Map.Entry<String, String> entry : processIDDefinitions.entrySet()) { 
            String key = entry.getKey();
            String value = entry.getValue();            
            varlist += "\n\n" + key + " == \n" + value;
        }
                
        for(int i=0;i<listOfDefinitions.size();i++)
        {   String ps = listOfDefinitions.get(i).substring(0,listOfDefinitions.get(i).indexOf("=="));
        	
        	// 7 == "ProcSet".length()
        	if(ps.contains("ProcSet") && (!(ps.length() == 7))){
        		varlist += "\n\n" + listOfDefinitions.get(i);
        		break;
        	}
        }
        
        for(int i=0;i<listOfDefinitions.size();i++)
        {   String ps = listOfDefinitions.get(i).substring(0,listOfDefinitions.get(i).indexOf("=="));
        	
        	if(!ps.contains("ProcSet"))        		
        		varlist += "\n\n" + listOfDefinitions.get(i);        	
        }
        
//*** definitions to be added for the range of identities of each process
        varlist += "\n\nInit == ";
        list = "";
        for (Map.Entry<String, String> entry: varList.entrySet()) {
            String key = entry.getKey();
            String value = entry.getValue();
            if(key.startsWith("?"))
            {
                list +="\n" + oneTab + "/\\ " + value;
            }
            else
            {
                list +="\n" + oneTab + "/\\ " + key + " = " + value;
            }
        }
        varlist += list;
        varlist += constantInitForTLAFile;
        return varlist;
    }
    
    public void addRangeDefinition(String name, String value)
    {
        processIDDefinitions.put(name, value);
    }

    private void reArrangeStatements(Map<Object, Statement> statements)
    {
        Map<Object, Statement> sts = new LinkedHashMap<Object, Statement>();
        Map<Object, Statement> stsUpdations = new LinkedHashMap<Object, Statement>();
        for (Map.Entry<Object, Statement> entry: statements.entrySet()) {
            Object key = entry.getKey();
            Statement value = entry.getValue();
            if(value.typeName.equals("updation") && (value.lHS.startsWith("PrintT(") || value.lHS.startsWith("_pc")))
            {
                stsUpdations.put(key, value);
            }
            else if(value.typeName.equals("updation"))
            {
            	for (Map.Entry<Object, Statement> entry2: stsUpdations.entrySet()) {
                    Object key2 = entry2.getKey();
                    Statement value2 = (Statement)entry2.getValue();
                    sts.put(key2, value2);
                }
                stsUpdations.clear();
                sts.put(key, value);
            }
            else
            {
                sts.put(key, value);
            }
        }
        statements.clear();
        statements.putAll(sts);
    }

    public String getLabelDescrption()
    {
        String text = "";
        String tab = "";
        for (Map.Entry<String, ActionStructure> entry: actions.entrySet()) {
            boolean pcUpdationStatementFound = false;
            boolean pcCurrentStatementAdded = false;
            boolean pcStatementFound = false;
            boolean gardeAdded = false;
            boolean isFirstStatementOfCase = false;
            boolean isFirstStatementOfCaseOfForLoop = false;
            boolean startOfBranch = false;
            boolean branchPossibleAfterAssignments = false;
            boolean branchWithinFor = false;	//If there is a branch statement inside a for loop then its indentation should be different
            int ifcount_ForLoop = 0;
            String key = entry.getKey();
            ActionStructure action = entry.getValue();
			ArrayList<String> positionOfThenSeen = new ArrayList<String>();
			ArrayList<String> positionOfCaseSeen = new ArrayList<String>();
			
			//rearrage statements, statements for updations should be at the end
            reArrangeStatements(action.statements);
            //
            if(action.hasSelf)
            {
                text += key + "(self) == \n";
                tab = "          ";
            }
            else if(!action.isDefinition)
            {
                
                text += key + " == \n";
                tab = "    ";
            }
            //Add spaces equal to the length of action name...
            for(int k=0;k<key.length();k++)
            {
                tab += " ";
            }
            //tab = "\t";
            
			positionOfThenSeen.clear();       	
			positionOfCaseSeen.clear();       	
            for (Statement value : action.statements.values()) {     
                if(!pcCurrentStatementAdded && ( ((!value.typeName.equals("updation")) || (value.lHS.startsWith("PrintT("))) && (!value.typeName.equals("definition")) ))
                {
                    pcCurrentStatementAdded = true;
                    text += tab;
                    text += "/\\ ";
                    text += action.pcID + " = \"" + key + "\"\n";                    
                }
                
				
				
				if(value.typeName.equals("guard"))
                {
                    text += tab;
                    text += "/\\ ";
                    text += value.lHS + "\n";                    
                }
				else if(value.lHS.equals("print"))	//generates print statement to be added to the TLA code
				{
                    text += tab; 
                    if(!gardeAdded)
                    {
                        text += "/\\ ";
                    }
					else
						text += "   ";
					
					text += value.rHS + "\n";  
					tab += "   ";    
					gardeAdded = false;		//enforces guard to be added after the print statement for the following statements        		                		
				}
                else if(value.typeName.equals("auxstatement") || value.typeName.equals("statement") || value.typeName.equals("with"))
                {	
                    text += tab;                		                		
                	if((pcCurrentStatementAdded && !gardeAdded) || isFirstStatementOfCase)
                    {
                        if(isFirstStatementOfCaseOfForLoop)
                        {
                            text += "THEN "; positionOfThenSeen.add(tab);
                            isFirstStatementOfCaseOfForLoop = false;
                            tab += "     ";
                        }
                        text += "/\\ ";
                        
                        gardeAdded = true;
                        isFirstStatementOfCase = false;
                    }
                    else
                    {
                           	text += "   ";
                    }
                    
					if(value.lHS.endsWith("_stack") && (value.rHS).endsWith("_pc |->"))
					{
						if(!action.callReturnPCID.equals(""))
							text += "LET " + value.lHS + " == " + value.rHS + action.callReturnPCID + "]>>)] IN\n";
						else
							text += "LET " + value.lHS + " == " + value.rHS + action.nextPC + "]>>)] IN\n";
					}
                    else if(value.lHS.equals(""))// adds the with statement to the description rHS contains is in the form => \E k \in {88, 99, 33, 55}:
                    {
						text += (!gardeAdded) ? "/\\ " : "";
                        text += value.rHS + "\n";       
	                }
                    else
                    {   //FIXME: Problem with the translation of bidimensional arrays
                    	//info is missed in value.lHS
                    	
                    	text += "LET " + value.lHS + " == " + value.rHS + " IN\n";                        	
                    }
                    branchPossibleAfterAssignments = true;
                    if(value.lHS.equals("__pc"))
                    {
                        pcStatementFound = true;
                    }
                }
                else if(value.typeName.equals("branch"))
                {
                    if(branchPossibleAfterAssignments)
                    {
                        branchPossibleAfterAssignments = false;
                    }
                    //System.out.println(value.isBranch);
                    //if(value.isBranch)
                    {
                        text += tab;
                    }
                    if(!gardeAdded)
                    {
                        text += "/\\ ";
                    }
                    else if(action.isForLoop)
                    {
                        text += "   /\\ ";
                        //tab += "   ";
                    }
                    else
                    {
                        text += "   ";
                    }
                    startOfBranch = true;
                    
                    if(action.isForLoop)
                    {
						//Code to be removed
//                    	if(ifcount_ForLoop>1)
//                    	{
//                    		branchWithinFor = true;
//                    	}
                        ifcount_ForLoop ++;
                    }
                }
                else if(value.typeName.equals("case"))
                {
                    if(startOfBranch)
                    {
                        startOfBranch = false;
                        tab += "         ";
                        if(value.isBranch)
                        {
                            text += "\\/ /\\ ";
							positionOfCaseSeen.add(tab); branchWithinFor = true;
                        }
                        else
                        {	
                            text += "IF ";
                            isFirstStatementOfCaseOfForLoop = true;
                        }
                    }
                    else
                    {
                        tab  = tab.substring(0, tab.length()-6);
						if(positionOfCaseSeen.size() > 0)//Enforces Else to be on the same column as its THEN
						{	
							tab = positionOfCaseSeen.get((positionOfCaseSeen.size()-1));
							//Branch statement inside a for statement is 3 places different than a branch outside a for loop
							if(action.isForLoop)
								tab  = tab.substring(0, tab.length()-3);
							else
								tab  = tab.substring(0, tab.length()-6);
	                    }
						
                        text += tab;
                        tab += "      ";
                        if(value.isBranch)
                        {
                            text += "\\/ /\\ "; branchWithinFor = true;
                        }
                        else
                        {
                            text += "ELSE IF ";
                        }
                    }                   
                    text += value.condition + "\n";
                    isFirstStatementOfCase = true;
                    gardeAdded = false;
                }
                else if(value.typeName.equals("end"))
                {   
					if(positionOfCaseSeen.size() > 0 && value.isBranch)//Enforces Else to be on the same column as its THEN
					{	
						positionOfCaseSeen.remove((positionOfCaseSeen.size()-1)); branchWithinFor = false;
					}
                    if(tab.length() > 10)
                    {
                        if(action.isForLoop)
                        {
                            tab = tab.substring(0, tab.length()-5);
                        }
                        tab = tab.substring(0, tab.length()-9);
                    }
                }
                else if(value.typeName.equals("else"))
                {
                    tab = (tab.substring(0, tab.length()-5));  
					if(positionOfThenSeen.size() > 0)//Enforces Else to be on the same column as its THEN
					{	
						tab = positionOfThenSeen.get((positionOfThenSeen.size()-1));
						positionOfThenSeen.remove((positionOfThenSeen.size()-1));
                    }
					text += tab + "ELSE\n";
                    tab += "     ";
                }
                else if(value.typeName.equals("definition"))
                {
                    String defName = key.substring(key.indexOf("_")+1, key.length());
                    String aux = defName + value.rHS + " == ";
                    String spaces = "";
                    
                    for(int i = 0;i < aux.length();i++)
                    	spaces += " ";
                    text += aux;
                    
                    if(value.lHS.contains("LET")){
                    	text += "\n ";
                    	text += value.lHS + "\n\n";
                	}else{
                		String sp = " ";
                        if(!(value.lHS.indexOf("\n") == -1)){                    	
                        	String tmp = "";
                        	tmp += value.lHS.substring(0, value.lHS.indexOf("\n")) + "\n" + spaces + " ";
                        	int j = value.lHS.indexOf("\n", value.lHS.indexOf("\n")+1);
                        	                    	
                        	while(j >= -1){                    		
                        		if(value.lHS.indexOf("\n", j+1) > -1){	
                        			tmp += tmp + sp + value.lHS.substring(j+1, value.lHS.indexOf("\n", j+1)).trim() + "\n";                    		                    			
                        			j = value.lHS.indexOf("\n", j+1);
                        			sp += " ";
                        		}else{                    			
                        			tmp = tmp.trim() + "\n" + spaces + sp + " " + value.lHS.substring(j+1).trim();
                        			break;
                        			}                    		                    		
                        	}	
                        	text += tmp + "\n\n";                 	
                        }else
                        	text += value.lHS + "\n\n";
                	}
                }
                else if(value.typeName.equals("updation"))
                {int ii = 0;
                    gardeAdded = false;
                    if(isFirstStatementOfCaseOfForLoop)
                    {
                        text += tab + "";
                        text += "THEN ";  
						positionOfThenSeen.add(tab);
                        isFirstStatementOfCaseOfForLoop = false;
                        tab += "     ";
                        gardeAdded = true; ii++;
                    }


                    if(value.lHS.equals(""))
                    {
                        text += tab + "   ";
                        text+= " " + value.rHS + " \n";                        
                    }
                    else if(value.rHS.equals("") && !value.lHS.equals("UNCHANGED"))
                    {
                        text+= tab + "   " + "/\\ " + value.lHS + " \n";
                    }
                    else
                    {
                        if(ifcount_ForLoop == 3 && action.isForLoop)
                        {
                            text += "   ";
                            if(branchWithinFor)
                            {
                            	text += tab; //Commented because it was adding too many tabs in one of the statements in the nested for loop
                            	//branchWithinFor = false;
								//System.out.println("its changing it to false");
                            }								
								
                            //text += tab + "  m ";
                            ifcount_ForLoop++;
                        }
                        else if(!gardeAdded)
                        {
                            text += tab + "   ";
                        }
                        else
                        {
                        	text += "   ";    	
                        }
                        
						if(!pcCurrentStatementAdded)
                        {
                            pcCurrentStatementAdded = true;
                            text += "/\\ ";
                            text += action.pcID + " = \"" + key + "\"\n";
                        }
                        
						if(value.lHS.equals(action.pcID) || action.pcID.startsWith(value.lHS))
                        {
                            pcUpdationStatementFound = true;
                        }
                        
						
						if(value.lHS.equals("UNCHANGED"))
                        {
                            if(!pcUpdationStatementFound && !action.pcID.equals("") && !action.nextPC.equals(""))
                            {
                                text += "/\\ ";
                                text += createPCAssignmentWithExcept(action.pcID, action.nextPC, pcStatementFound);
                                pcStatementFound = false;
                                text += tab + "   ";
                            }
                            text += "/\\ ";
                            text += value.lHS;
                            text+= " << " + calculateUnchangedVars(value.rHS, "_pc[self]") + " >>\n";
                            pcUpdationStatementFound = false;
                        }
                        else if(value.lHS.equals(""))
                        {
                            text+= " " + value.rHS + " \n";                            
                        }
                        else //Adds all the set of statements for variables that are changed.
                        {	
							text += "/\\ ";
                            text += value.lHS;                            
                            text+="' = " + value.rHS + "\n";                            
                        }
                    }
                }
            }
        }
        text += "\nNext == ";

        if(isMainActive)
        {
            text += "_Main(0) \n                  \\/ ";
        }

        if(listOfAllProcessIDs != null)
        {
        	for (Map.Entry<String, String> entry: listOfAllProcessIDs.entrySet()){
                String key = entry.getKey();
                String value = entry.getValue();

				if(!noStatementProcess.contains(value))
				{
	                text += "(\\E self \\in " + value + " : _" + key + "(self))\n";
	                text += tab + oneTab + "\\/ ";
				}
            }

            text += "(";
            if(isMainActive)
            {
                text += "_pc[0] = \"Done\"\n";
                text += tab + oneTab + oneTab + "/\\ ";
            }
            text += "(\\A self \\in ProcSet : _pc[self] = \"Done\")\n";

            text += tab + oneTab + oneTab;
            text += "/\\ UNCHANGED vars)\n";
        }
        else
        {
                text += tab + oneTab;
                text += "\\/ (_pc[0] = \"Done\"  /\\ UNCHANGED vars)\n";
        }
        
        text += "\nSpec == Init /\\ [][Next]_vars\n";
        return text;
    }
    
    private String createPCAssignmentWithExcept(String pcid, String nextpc, boolean pcStatementFound)
    {
        String newID = "";
        if(pcid.contains("[") && !pcStatementFound)
        {
            String varName = pcid.substring(0, pcid.indexOf("["));
            String extension = pcid.substring(pcid.indexOf("["));
            newID = varName + "' = [" + varName + " EXCEPT !" + extension + " = " + nextpc + "]\n";
        }
        else if(pcid.contains("[") && pcStatementFound)
        {
            String varName = pcid.substring(0, pcid.indexOf("["));
            String extension = pcid.substring(pcid.indexOf("["));
            newID = varName + "' = [_" + varName + " EXCEPT !" + extension + " = " + nextpc + "]\n";
        }
        else
        {
            newID = pcid+ "' = " + nextpc + "\n";
        }
        
        return newID;        
    }
    private String calculateUnchangedVars(String changedVars, String pcID)
    {
        String unChangevariables = "";
        String[] arChangedVariables = changedVars.split(" ");
        Iterator it = varList.entrySet().iterator();
        pcID = pcID.substring(0,pcID.indexOf("["));
        while (it.hasNext()) {
            Map.Entry variableEntry = (Map.Entry) it.next();
            String variableName = variableEntry.getKey().toString();
            if(variableName.startsWith("?"))
            {
                variableName = variableName.substring(1, variableName.length());
            }
            boolean isChangedVariable = false;
            for (String changedVariableName : arChangedVariables) {
                
                if ((changedVariableName.equals(variableName)) || (variableName.equals(pcID))) {
                    isChangedVariable = true;
                }
            }
            if ((!isChangedVariable)) {
                unChangevariables += ", " +variableName;
            }
            
        }
        
        unChangevariables = unChangevariables.replaceFirst(", ", "");
        
        return unChangevariables;
    }
    public String getPropertyDescription()
    {
        String desc = "";
        if(invariantList.size() > 0)
        {
            for(int i=0;i<invariantList.size();i++)
            {
                desc += "Inv" + i + " == " + invariantList.get(i) + "\n";
            }
        }
        if(temporalList.size() > 0)
        {
            for(int i=0;i<temporalList.size();i++)
            {
                desc += "Temp" + i + " == " + temporalList.get(i) + "\n";
            }
        }
        if(constraintList.size() > 0)
        {
            for(int i=0;i<constraintList.size();i++)
            {
                desc += "Const" + i + " == " + constraintList.get(i) + "\n";
            }
        }
        
        return desc;
    }
    public int getNumOfProperties(String type)
    {
        int num = 0;
        if(type.equals("temporal"))
        {
            num = temporalList.size();
        }
        else if(type.equals("invariant"))
        {
            num = invariantList.size();
        }
        else if(type.equals("constraint"))
        {
        	num = constraintList.size();
        }
        return num;
    }
    public String getFairnessDescription()
    {
        String desc = "";
        String tab = "    ";
        if(fairList.size() > 0)
        {
            desc = "Fairness == \n";
            for (Map.Entry<String, String> entry : fairList.entrySet()) {
                String key = entry.getKey();
                String value = entry.getValue();
                desc += tab;
                if(value.compareToIgnoreCase("weak") == 0)
                {
                    desc += createFairnessStatement(key, "weak");
                }
                else
                {
                    desc += createFairnessStatement(key, "strong");
                }
                
            }
        }
        
        return desc;
    }
    public String createFairnessStatement(String key, String type)
    {
        String statement = "";
        String labelName = "";
        String setName = "";
        boolean belongsToMain = false;
        
        if(key.contains(":"))
        {
            String[] vals = key.split(":");
            if(vals.length == 1)//belongs to global function
            {
                labelName = vals[0];
                statement += "/\\ \\A self \\in ProcSet : ";
            }
            else if(vals.length == 2 && vals[0].equals(""))//belongs to main algorithm
            {
                labelName = vals[1];
                belongsToMain = true;
                statement += "/\\ ";
            }
            else//belongs to process or thread
            {
                setName = vals[0];
                labelName = vals[1];
                statement += "/\\ \\A self \\in " + setName + " : ";
            }
            
            if(type.equals("weak"))
            {
                if(belongsToMain)
                {
                    statement += "/\\ WF_vars(" + labelName + "(0))\n";
                }
                else
                {
                    statement += "/\\ WF_vars(" + labelName + "(self))\n";
                }
            }
            else
            {
                if(belongsToMain)
                {
                    statement += "/\\ SF_vars(" + labelName + "(0))\n";
                }
                else
                {
                    statement += "/\\ SF_vars(" + labelName + "(self))\n";
                }
            }
        }
        else
        {key = key.substring(1, key.length());
            if(type.equals("weak"))
            {
                statement = "/\\ \\A self \\in " + listOfAllProcessIDs.get(key) + " : /\\ WF_vars(_" + key + "(self)) \n";
            }
            else
            {
                statement = "/\\ \\A self \\in " + listOfAllProcessIDs.get(key) + " : /\\ SF_vars(_" + key + "(self)) \n";
            }
        }
        
        return statement;
    }
    public String getConstantDefInfo()
    {
        return constantInitForConfigFile;
    }

    public void showTree(){
    
    	for (Map.Entry<String, ActionStructure> entry:actions.entrySet()) {
            String key = entry.getKey();
            ActionStructure value = entry.getValue();
            System.out.println("-----------------------------");
            System.out.println("label name:" + key);
            System.out.println("NextPC value:" + value.nextPC);
            for (Statement key2 : value.statements.values()) {
                if(key2.typeName.equals("statement"))
                    System.out.println(key2.lHS + " := " + key2.rHS);
                else if(key2.typeName.equals("case"))
                    System.out.println("Case:" + key2.condition);
                else if(key2.typeName.equals("auxstatement"))
                    System.out.println(key2.lHS + " = " + key2.rHS);
                else if(key2.typeName.equals("branch"))
                    System.out.println("Branch--");
                else if(key2.typeName.equals("end"))
                    System.out.println("end--");
                else if(key2.typeName.equals("else"))
                    System.out.println("else");
                else if(key2.typeName.equals("updation"))
                    System.out.println(key2.lHS + " = " + key2.rHS);
                else if(key2.typeName.equals("with"))
                    System.out.println("This is with" + key2.lHS + " = " + key2.rHS);
            }
            
        }
    }
    
    //**************************** Independence Matrix Generation Code ***********************************//
    
    /**
     * Checks if the string str is a number
     */
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
     * Confirms the existences of variable var in the given string str.
     * @param str the string the might contain the variable
     * @param var the variable to be searched
     * @return true if variable found otherwise false
     */
    private boolean confirmVariable(String str, String var)
    {
    	char ccend;
    	char ccstart;
    	int lastIndex = str.indexOf(var) + var.length();
    	
    	if(lastIndex == -1)
    		return false;
    	else if(lastIndex >= str.length())
    	{
    		if(str.equals(var))
    			return true;
    		else
    			return false;
    	}
    	
    	ccend = str.charAt(lastIndex);
    	if(lastIndex - var.length() - 1 >= 0)
    		ccstart = str.charAt(lastIndex - var.length() - 1);
    	else
    		ccstart = ':';

    	while(true)
    	{
	    	if((ccend < 'a' || ccend > 'z') && (ccend < 'A' || ccend > 'Z') && (ccend < '0' || ccend > '9'))
	    		return true;
	    	lastIndex = str.indexOf(var, lastIndex);
	    	if(lastIndex != -1)
	    	{
	    		lastIndex += var.length();
	    		ccend = str.charAt(lastIndex);
	        	if(lastIndex - var.length() - 1 >= 0)
	        		ccstart = str.charAt(lastIndex - var.length() - 1);
	        	else
	        		ccstart = ':';
	    	}
	    	else
	    		break;
    	}
    	return false;
    }
    /**
     * Constructs the LetIn statements for a given expression by checking if it contains a variable that is updated in the
     * previous statements
     * @param expression The expression 
     * @param mapping The set of mapping for the variables and their new expressions or values
     * @return The new expression with LetIn statements
     */
    private String constructLETINstatementsold(String expression, LinkedHashMap<String, String> mapping)
    {
    	String LETstatements = "";
		boolean flag = true;
		String temp = expression;
		String varsToIgnore = "";
		System.out.println("-------------------Searching for : " + expression);
		while(flag)
		{
			flag = false;
						
			Set<Entry<String, String>> entryset = mapping.entrySet();
			Entry<String, String>[] entry = new Entry[entryset.size()]; 
			entryset.toArray(entry);
			
			for (int i = entry.length-1;i>=0;i--) 
			{
				String key = entry[i].getKey();
				if(searchVariable(key, entry[i].getValue(), temp)&& !varsToIgnore.contains(":" + key + ":"))
				{
					System.out.println(key + "   " + entry[i].getValue());
					LETstatements = "LET " + key + " == " + entry[i].getValue() + " IN " + LETstatements ;
			    	varsToIgnore += ":" + key + ":";
			        flag = true;
				}
			    else
			     continue;
			}
			temp = LETstatements;
		}
    	return LETstatements;
    }
    private String constructLETINstatements(String expression, LinkedHashMap<String, String> mapping)
    {
    	String LETstatements = "";
		boolean flag = true;
		String temp = expression;
		String varsToIgnore = "";

		LinkedHashMap<String, String> tempMap = new LinkedHashMap<String, String>();
		while(flag)
		{
			flag = false;
						
			Set<Entry<String, String>> entryset = mapping.entrySet();
			Entry<String, String>[] entry = new Entry[entryset.size()]; 
			entryset.toArray(entry);
			
			for (int i = entry.length-1;i>=0;i--) 
			{
				String key = entry[i].getKey();
				if(searchVariable(key, entry[i].getValue(), temp)&& !varsToIgnore.contains(":" + key + ":"))
				{
					tempMap.put(key, entry[i].getValue());
					LETstatements = "LET " + key + " == " + entry[i].getValue() + " IN " + LETstatements ;
			    	varsToIgnore += ":" + key + ":";
			        flag = true;
				}
			    else
			     continue;
			}
			temp = LETstatements;
		}
		
		//If no LETIN statements required then it should return 
		if(LETstatements.equals(""))
		{
			expression = searchAndReplace(expression, null);
			return expression;
		}
		
		//If LetIn statements found then it should check and fix the names of the variables 

		LETstatements = "";
		Set<Entry<String, String>> entryset = tempMap.entrySet();
		Entry<String, String>[] entry = new Entry[entryset.size()]; 
		entryset.toArray(entry);
		

		String lastKey = "";
		Map<String, String> lastKeyList = new LinkedHashMap<String, String>();
		for (int i = entry.length-1;i>=0;i--) 
		{
			String key = entry[i].getKey();
			String value = entry[i].getValue();
			
			if(key.startsWith("__") && key.endsWith("_data") && value.contains(" EXCEPT "))
			{//Assuming the its an assignment to a process local variable
			 //Example: ___proc_data == [__proc_data EXCEPT ![_q].x = __proc_data[_q].j]
				String var = value.substring(1, value.indexOf(" "));
				String newVar = checkInList(var, lastKeyList, true);
				value = replaceVariableNames(value, var, newVar);
				value = searchAndReplace(value, lastKeyList);
				lastKeyList = addVartoLastKeyList(key, lastKeyList, true);
				
			}
			else
			{
				value = searchAndReplace(value, lastKeyList);
				//The global variables should be added to list as well and must be checked
			}
			if(parameters.contains(key))
			{
				key = "_" + key;
			}
			LETstatements += "LET " + key + " == " + value + " IN ";
		
		}
		
		expression = searchAndReplace(expression, lastKeyList);
		/*
		while(expression.contains("_"+lastKey))
		{
			int index = expression.indexOf("_"+lastKey);
			if(index > -1)
			{
				expression = expression.replace("_"+lastKey, lastKey);
			}
		}*/
		LETstatements +=  expression ;

    	return LETstatements;
    }
    
    private String searchAndReplace(String exp, Map<String,String> list)
    {
    	int i = 0;
    	int index = 0;
    	char ch;
    	String var;
    	
   
    	while(i<exp.length())
    	{    	
    		index = exp.indexOf("__", i);
    		if(index == -1)
    			break;
    		i = index;
    		while(i<exp.length())
    		{
    			ch = exp.charAt(i);
		    	if((ch < 'a' || ch > 'z') && (ch < 'A' || ch > 'Z') && (ch < '0' || ch > '9') && ch != '_')
		    	{
		    		break;
		    	}
		    	i++;
    		}
    		var = exp.substring(index, i);
    		boolean flag= false;
    		if(list != null)
    		{
	        	for (Map.Entry<String, String> entry: list.entrySet()){
	                String key = entry.getKey();
	                if(matchVariable(var, key))
	                {
	                	flag = true;
	                	exp = exp.substring(0, index) + key + exp.substring(i, exp.length());
	                	break;
	                }
	        	}
    		}
        	if(!flag)//if the variable var is new then it should only have single "_"
        	{
            	while(var.startsWith("_"))
        		{
            		var = var.substring(1, var.length());
        		}
            	var = "_" + var;
            	exp = exp.substring(0, index) + var + exp.substring(i, exp.length());
        	}
    	}
    	return exp;
    }
    
    private boolean matchVariable(String var1, String var2)
    {
    	while(var1.startsWith("_"))
		{
    		var1 = var1.substring(1, var1.length());
		}
    	while(var2.startsWith("_"))
		{
    		var2 = var2.substring(1, var2.length());
		}
    	if(var1.equals(var2))
    		return true;
    	return false;
    }
    
    private String checkInList(String var, Map<String, String> list, boolean flag)
    {
    	for (Map.Entry<String, String> entry: list.entrySet()){
            String key = entry.getKey();
            String value = entry.getValue();
            if(matchVariable(var, key))
            	return value + key;
    	}
    	while(var.startsWith("_"))
		{
    		var = var.substring(1, var.length());
		}
    	if(flag)
    	{
    		var = "_" + var;
    	}
    	
    	return var;
    }
    
    private Map<String, String> addVartoLastKeyList(String var, Map<String, String> list, boolean flag)
    {
    	
    	for (Map.Entry<String, String> entry: list.entrySet()){
            String key = entry.getKey();
            String value = entry.getValue();
            if(matchVariable(var, key))
            {
            	list.remove(key);
            	list.put(var, "");
            	return list;
            }
    	}
    	
    	list.put(var, "");
    	
    	return list;
    }
    
    /**
     * Search a local process variable in a given expression. 
     * @param lhs
     * @param rhs
     * @param expression
     * @return
     */
    private boolean searchVariable(String lhs, String rhs, String expression)
    {
    	String extension = "";
    	try
    	{
		extension = rhs.substring(rhs.indexOf("!")+1, rhs.indexOf("=")-1);
    	}
    	catch(Exception e)
    	{

    	}
		
		if(lhs.startsWith("__") && lhs.endsWith("_data"))
		{
			while(lhs.startsWith("_"))
			{
				lhs = lhs.substring(1, lhs.length());
			}
			lhs = "_" + lhs + extension;
			if(expression.contains(lhs))
				return true;
			
		}
		else if(expression.contains(lhs))
		{
			return true;
		}
    	return false;
    }
    /**
     * It replaces the variable names in a given expression with a specified variable
     * @param completeStr The expression
     * @param searchStr The variable to be changed
     * @param replacementStr The new variable
     * @return The new expression
     */
    private String replaceVariableNames(String completeStr, String searchStr, String replacementStr)
    {
    	if(completeStr.equals(searchStr))
    	{
    		return replacementStr;
    	}
		 String[] strl = completeStr.split("[^a-zA-Z0-9]{1}" + searchStr +"[^a-zA-Z_0-9]{1}");
		 
		 int i = 0;
		 int pos = 0;
		 String finalStr = "";
		 while(i<strl.length-1)
		 {
			 pos += strl[i].length();
			 finalStr += strl[i] + completeStr.charAt(pos) + replacementStr + completeStr.charAt(pos+searchStr.length()+1);
			 i++;
			 pos += searchStr.length() + 2;
		 }
		 finalStr += strl[i];
		 return finalStr;
    }
    /**
     * Creates the predicate for any given expressions.
     * @param exprA First expression
     * @param exprB Second expression
     * @return The predicate
     */
    private String createPredicateold(String exprA, String exprB)
    {
		//Check if they are numbers, then the predicate can be resolved 
		if(isNumber(exprA) && isNumber(exprB))
		{// return true because we already know that they are different
			return "TRUE";
		}
		
		String LETstatementsA = "";
		String LETstatementsB = "";
		
		LETstatementsA = constructLETINstatements(exprA, mappingForA);
		LETstatementsB = constructLETINstatements(exprB, mappingForB);

		LETstatementsA = replaceVariableNames(LETstatementsA, "self", parameters.get(0));
		LETstatementsB = replaceVariableNames(LETstatementsB, "self", parameters.get(1));
		
		//String predicate = LETstatementsA + LETstatementsB + exprA + " # " + exprB;
		String predicate = "(" + LETstatementsA + ") # (" + LETstatementsB + ")";
    	return predicate;
    }
    /**
     * Creates the predicate for any given expressions.
     * @param exprA First expression
     * @param exprB Second expression
     * @return The predicate
     */
    private String createPredicate(String exprA, String exprB)
    {
		//Check if they are numbers, then the predicate can be resolved 
		if(isNumber(exprA) && isNumber(exprB))
		{// return true because we already know that they are different
			return "TRUE";
		}

		exprA = replaceVariableNames(exprA, "self", parameters.get(0));
		exprB = replaceVariableNames(exprB, "self", parameters.get(1));
		
		//String predicate = LETstatementsA + LETstatementsB + exprA + " # " + exprB;
		String predicate = "(" + exprA + ") # (" + exprB + ")";
    	return predicate;
    }
    
    /**
     * Compares the extensions of two variables if extensions are .<field name> or [<expression>] e.g., .type, [self]
     * @param a
     * @param b
     * @return
     */
    private String compareExtensions(String a, String b)
    {
		// if extensions are .<field name> or [<expression>] e.g., .type, [self]
		if(a.equals(b) && !a.contains("_data[self]") && !a.equals("[self]"))
		{
			return "FALSE";
		}

		if(a.startsWith("[") && b.startsWith("[") && a.endsWith("]") && b.endsWith("]"))
		{
			a = a.substring(1, a.length()-1);
			b = b.substring(1, b.length()-1);
			
			return createPredicate(a, b);
		}

    	return "TRUE";
    }
    private boolean haveAppendTailOperations(String a, String b)
    {
    	String tempA = a.substring(a.indexOf("=")+2, a.length());
    	String tempB = b.substring(b.indexOf("=")+2, b.length());
    	
    	if(tempA.startsWith("Append(") && tempB.startsWith("Tail("))
    		return true;
    	else if(tempB.startsWith("Append(") && tempA.startsWith("Tail("))
    		return true;
    	
    	return false;
    }
    private String deepCompare(Statement a, Statement b)
    {
    	String rhsA = a.rHS, rhsB = b.rHS;
    	
    	//rhsA = replaceVariableNames(rhsA, "self", parameters.get(0));
    	//rhsB = replaceVariableNames(rhsB, "self", parameters.get(1));

    	//If they are both global variables and not arrays
    	if(!rhsA.contains("EXCEPT") && !rhsB.contains("EXCEPT"))
    	{
    		return "FALSE";
    	}
    	
    	if(rhsA.contains("EXCEPT") && rhsB.contains("EXCEPT"))
    	{//[_pro_data EXCEPT ![self].y = 7] OR [foo EXCEPT ![((__d + 6) + _proc_data[self].j)] = TRUE] OR ...
    		
    		//Compare the extension on the left hand side of the assignment statement
    		//Extract the extension after ! mark
    		String extensionA, extensionB;
    		extensionA = rhsA.substring(rhsA.indexOf("!")+1, rhsA.indexOf("=")-1);
    		extensionB = rhsB.substring(rhsB.indexOf("!")+1, rhsB.indexOf("=")-1); 
    		
    		if(isArrayAccess(extensionB) && isArrayAccess(extensionA))
    		{
    			if(haveAppendTailOperations(rhsA, rhsB))
    			{
    				return "TRUE";
    			}
    		}
    		return compareExtensions(extensionA, extensionB);
    	}
    	
    	return "TRUE";
    }
    
    private boolean isArrayAccess(String str)
    {
    	if(str.startsWith("[") && str.endsWith("]"))
    		return true;
    	else
    		return false;
    }
    
    private String deepCompareProcessVariableUpdate(Statement a, Statement b)
    {
    	String rhsA = a.rHS, rhsB = b.rHS;
    	    	
    	String extensionA, extensionB;
		extensionA = rhsA.substring(rhsA.indexOf("![self]")+7, rhsA.indexOf("=")-1);
		extensionB = rhsB.substring(rhsB.indexOf("![self]")+7, rhsB.indexOf("=")-1);    		
		
		extensionA = replaceVariableNames(extensionA, "self", parameters.get(0));
		extensionB = replaceVariableNames(extensionB, "self", parameters.get(1));

		String result = compareExtensions(extensionA, extensionB); 
		if(result.equals("FALSE"))
			return parameters.get(0) + " # " + parameters.get(1);
		else
			return result;
			
    }
    
    private String compareStatements(Statement a, Statement b)
    {
    	if(!a.lHS.equals(b.lHS))// && ((!a.lHS.startsWith("__") && !a.lHS.endsWith("_data")) || (!b.lHS.startsWith("__") && !b.lHS.endsWith("_data"))))
    	{
    		String temp1 = a.lHS;
    		String temp2 = b.lHS;
    		while(temp1.startsWith("_"))
    		{
    			temp1 = temp1.substring(1, temp1.length());
    		}
    		while(temp2.startsWith("_"))
    		{
    			temp2 = temp2.substring(1, temp2.length());
    		}
    		if(!temp1.equals(temp2))
    			return "TRUE";
    	}
    	//If the two updations belong to same process, then the variables should be checked
    	if(a.lHS.startsWith("__") && a.lHS.endsWith("_data") && b.lHS.startsWith("__") && b.lHS.endsWith("_data"))
    	{
    		String temp1 = a.lHS.replaceAll("_", "");
    		temp1 = temp1.substring(0, temp1.length()-4);
    		String temp2 = b.lHS.replaceAll("_", "");
    		temp2 = temp2.substring(0, temp2.length()-4);
    		
    		if(temp1.equals(temp2))
    		{
    			return deepCompareProcessVariableUpdate(a, b);
    		}
    	}
    	//We know that variables are same, now we need to check if they are arrays then indexes should be different
   		return deepCompare(a, b);
    	
    }
    
    private LinkedHashMap<String, String> mappingForA = new LinkedHashMap<String,String>();
    private LinkedHashMap<String, String> mappingForB = new LinkedHashMap<String,String>();
    private ArrayList<String> parameters = new ArrayList<String>();

    private ArrayList<String> performAndOperation(ArrayList<String> temp1, ArrayList<String> temp2)
    {
    	
    	if(temp1.isEmpty())
    		return temp2;

    	for(int i=0;i<temp2.size(); i++)
    	{
    		temp1.add(temp1.size(), temp2.get(i));
    	}
    	return temp1;
    }
    private ArrayList<String> normalize(ArrayList<String> temp1)
    {
    	if(temp1.isEmpty())
    		return temp1;

    	ArrayList<String> temp = new ArrayList<String>();
    	
    	String predicate = "";
    	boolean flag = true;
    	int len = 0; int lastLen = 0;
    	
    	for(int i=0;i<temp1.size(); i++)
    	{
    		String str = temp1.get(i);
    		if(str.startsWith(" /\\ "))
    		{
    			predicate += str;
    			len += str.length();
    			lastLen = str.length();
    		}
    		else if(flag)
    		{
    			flag = false;
    			temp.add(predicate);
    			len -= lastLen;
    			temp.add(getSpaces(len) + str);
    		}
    		else
    		{
    			temp.add(getSpaces(len) + str);
    		}
    		
    	}
    	if(flag)
    	{
    		temp.add(predicate);
    	}
    	return temp;
    }
    /**
     * indep(A1,A2)
     * @param a
     * @param b
     * @param prefix
     * @return
     */
    private ArrayList<String> compareBlocks(Map<Object, Statement> a, Map<Object, Statement> b, String prefix)
    {
    	boolean isSkipBlock = true;
    	boolean hasBranch = false;

        Iterator<Map.Entry<Object, Statement>> iter;
        ArrayList<String> predicates = new ArrayList<String>();
        LinkedHashMap<String, String> mapping = new LinkedHashMap<String,String>();
        
        for (iter = a.entrySet().iterator(); iter.hasNext();)
        {
            Map.Entry<Object, Statement> entry = (Map.Entry<Object, Statement>)iter.next();
            Statement value = (Statement)entry.getValue();
            
            if(value.typeName.equals("statement"))
            {
            	isSkipBlock = false;

            	mapping.put(value.lHS, replaceVariableNames(value.rHS, "self", parameters.get(0)));
            	mappingForA.putAll(mapping);
            	
            	ArrayList<String> temp =compareWithB(value, b);
            	
            	if(temp.size() == 1 && temp.contains(" /\\ FALSE"))
            	{
            		return temp;
            	}
            	temp = normalize(temp);
            	predicates = performAndOperation(predicates, temp);
            }
            else if(value.typeName.equals("branch"))
            {
            	hasBranch = true;
            	isSkipBlock = false;
            	if(mapping.size() > 0)
            	{
            		pTree.setLetInStatements(mapping);
            	}
        		entry = (Map.Entry<Object, Statement>)iter.next();
        		value = (Statement)entry.getValue();
        		String condition = replaceVariableNames(value.condition, "self", parameters.get(0));

        		int count = 0;
            	Map<Object, Statement> new_a = new LinkedHashMap<Object, ExplodedTree.Statement>();
            	while(iter.hasNext())
            	{
            		entry = (Map.Entry<Object, Statement>)iter.next();
            		value = (Statement)entry.getValue();
            		if(value.typeName.equals("case") || value.typeName.equals("end"))
            		{
            			pTree.addCondition(condition);
            			mapping.clear();
            			ArrayList<String> temp = compareBlocks(new_a, b, "");
            			pTree.close();
            			
            			predicates.addAll(combinePredicateCondition(temp, "(" + constructLETINstatements(condition, mapping) + ")"));
            			condition =  replaceVariableNames(value.condition, "self", parameters.get(0));
            			new_a.clear();
            			continue;
            		}
            		else if(value.typeName.equals("branch"))
            		{
            			new_a.put(entry.getKey(), entry.getValue());
            			count++;
            			while(iter.hasNext() && count > 0)
                    	{
                    		entry = (Map.Entry<Object, Statement>)iter.next();
                    		value = (Statement)entry.getValue();
                    		if(value.typeName.equals("branch"))
                    			count++;
                    		else if(value.typeName.equals("end"))
                    			count--;
                    		new_a.put(entry.getKey(), entry.getValue());
                    	}
            			continue;
            		}
            		else
            			new_a.put(entry.getKey(), entry.getValue());
            	}
            }
            else if(value.typeName.equals("with"))
            {
            	isSkipBlock = false;
            	String withStatement = value.rHS.substring(3, value.rHS.length()-1);
            	entry = (Map.Entry<Object, Statement>)iter.next();
            	value = (Statement)entry.getValue();
            	withStatement += ": LET " + value.lHS + " == " + replaceVariableNames(value.rHS, "self", parameters.get(0)) + " IN ";

            	Map<Object, Statement> new_a = new LinkedHashMap<Object, ExplodedTree.Statement>();
            	while(iter.hasNext())
            	{
            		entry = (Map.Entry<Object, Statement>)iter.next();
            		value = (Statement)entry.getValue();
           			new_a.put(entry.getKey(), entry.getValue());
            	}
    			ArrayList<String> temp = compareBlocks(new_a, b, "");
    			predicates.addAll(combinePredicateCondition(temp, " /\\ (\\A " + constructLETINstatements(withStatement, mapping) + ")" ));

            }
            
        }
        if(isSkipBlock || predicates.isEmpty())
        {
        	pTree.addPredicate("TRUE");
        }
        
        if(!hasBranch)
        {
        	pTree.setLetInStatements(mapping);
        }

       	return predicates;
    }
    private ArrayList<String> combinePredicateCondition(ArrayList<String> predicate, String condition)
    {
    	condition = "/\\ ( " + condition + " => ";
    	
    	if(predicate.isEmpty() || (predicate.size() == 1 && predicate.contains("")))
		{
    		//Commented to avoid generating TRUE; Uncomment and comment the statement below to generate TRUE
    		//predicate.add(condition + " /\\ TRUE)"); 
    		condition += "TRUE)";
    		predicate.clear();
    		predicate.add(condition );
			return predicate;
		}
    	
    	predicate = indentCode(predicate, condition);
    	String str = predicate.get(predicate.size()-1);
    	str += "))";
    	predicate.set(predicate.size()-1, str);

    	return predicate;
    }
    private String getSpaces(int len)
    {
    	String spaces = "";
    	for(int j=0;j<len;j++)
    	{
    		spaces += " ";
    	}
    	return spaces;
    }
    private ArrayList<String> indentCode(ArrayList<String> temp, String condition)
    {
    	int i = 0;
    	//************** to add indentation in representation
    	temp.set(i, condition + "(" + temp.get(i));

    	for(i=1;i< temp.size();i++)
    	{
   			temp.set(i, getSpaces(condition.length()) + temp.get(i));
    	}
    	return temp;
    }
    /**
     * indep(S, A2)
     * @param statement1
     * @param b
     * @return
     */
    private  ArrayList<String> compareWithB(Statement statement1, Map<Object, Statement> b)
    {
    	boolean isSkipBlock = true;
    	boolean hasBranch = false;
        Iterator<Map.Entry<Object, Statement>> iter;
        ArrayList<String> predicates = new ArrayList<String>();
        String predicate = "";
        String withStatement = "";
        LinkedHashMap<String, String> mapping = new LinkedHashMap<String,String>();
        //mappingForB.clear();

        
        for (iter = b.entrySet().iterator(); iter.hasNext();)
        {
            Map.Entry<Object, Statement> entry = (Map.Entry<Object, Statement>)iter.next();
            Statement statement2 = (Statement)entry.getValue();
            
            if(statement2.typeName.equals("statement"))
            {
            	isSkipBlock = false;
            	String result = compareStatements(statement1, statement2);
            	mapping.put(statement2.lHS, replaceVariableNames(statement2.rHS, "self", parameters.get(1)));
            	mappingForB.putAll(mapping);

            	//**
            	if(result.equals("FALSE"))
            	{
            		pTree.cutBranch();
            		predicates.clear();
            		predicates.add(" /\\ " + result);
            		return predicates;
            	}
            	else if(!result.equals("TRUE"))// to avoid generating TRUE
            	{
            		pTree.addPredicate(result);
            		predicates.add(" /\\ " + result);
            	}

            }
            else if(statement2.typeName.equals("branch"))
            {
            	hasBranch = true;
            	if(mapping.size() > 0)
            	{
            		pTree.setLetInStatements(mapping);
            	}
            	isSkipBlock = false;
        		entry = (Map.Entry<Object, Statement>)iter.next();
        		statement2 = (Statement)entry.getValue();
        		String condition = replaceVariableNames(statement2.condition, "self", parameters.get(1));

        		int count = 0;
            	Map<Object, Statement> new_b = new LinkedHashMap<Object, ExplodedTree.Statement>();
            	while(iter.hasNext())
            	{
            		entry = (Map.Entry<Object, Statement>)iter.next();
            		statement2 = (Statement)entry.getValue();
            		if(statement2.typeName.equals("case") || statement2.typeName.equals("end"))
            		{
            			pTree.addCondition(condition);
            			mapping.clear();
            			ArrayList<String> temp = compareWithB(statement1, new_b);
            			pTree.close();
                  /*  	if(temp.size() == 1 && temp.contains(" /\\ FALSE"))
                    	{
                        	pTree.cutBranch();
                    		return temp;
                    	}*/
            			predicates.addAll(combinePredicateCondition(temp, "(" + constructLETINstatements(condition, mappingForB) + ")" ));
            			condition = replaceVariableNames(statement2.condition, "self", parameters.get(1));
            			new_b.clear();
            			continue;
            		}
            		else if(statement2.typeName.equals("branch"))
            		{
            			new_b.put(entry.getKey(), entry.getValue());
            			count++;
            			while(iter.hasNext() && count > 0)
            			{
                    		entry = (Map.Entry<Object, Statement>)iter.next();
                    		statement2 = (Statement)entry.getValue();
                    		if(statement2.typeName.equals("branch"))
                    			count++;
                    		else if(statement2.typeName.equals("end"))
                    			count--;
                    		new_b.put(entry.getKey(), entry.getValue());
                    	}
            			continue;
            		}
            		else
            			new_b.put(entry.getKey(), entry.getValue());
            	}
            }
            else if(statement2.typeName.equals("with"))
            {
            	
            	withStatement = statement2.rHS.substring(3, statement2.rHS.length()-1);
            	entry = (Map.Entry<Object, Statement>)iter.next();
            	statement2 = (Statement)entry.getValue();
            	String rhs = replaceVariableNames(statement2.rHS, "self", parameters.get(1));
            	//Temporarily renaming the auxillary variable 
            	withStatement = "_" +withStatement; 
            	rhs = rhs.replace(" = ", " = _");
            	rhs = replaceVariableNames(rhs, "__proc_data", statement2.lHS);
            	//****
            	withStatement += ": LET " + statement2.lHS + " == " + rhs + " IN ";
            	
            	isSkipBlock = false;

            	Map<Object, Statement> new_b = new LinkedHashMap<Object, ExplodedTree.Statement>();
            	while(iter.hasNext())
            	{
            		entry = (Map.Entry<Object, Statement>)iter.next();
            		statement2 = (Statement)entry.getValue();
           			new_b.put(entry.getKey(), entry.getValue());
            	}
    			ArrayList<String> temp = compareWithB(statement1, new_b);
    			predicates.addAll(combinePredicateCondition(temp, " /\\ (\\A " + constructLETINstatements(withStatement, mapping) + ")" ));

            }
        }

        if(isSkipBlock || predicates.isEmpty())
        {
        	pTree.addPredicate("TRUE");
        	//predicate = " /\\ TRUE"; Commented to avoid generating TRUE
        	predicate = "";
        	predicates.add(predicate);
        }
        else if(!predicates.isEmpty() && !withStatement.equals(""))
        {
        	//predicates = includeWith(withStatement, predicates);
        }
        
        if(!hasBranch)
        {
        	pTree.setLetInStatements(mapping);
        }
        
       	return predicates;
    }
    
    private boolean isIndepMatrixAlreadyDefined()
    {
    	int i=0;
    	while(i < listOfDefinitions.size())
    	{
    		String def = listOfDefinitions.get(i);
    		if(def.startsWith("IndepMatrix"))
    			return true;
    		i++;
    	}
    	return false;
    }
    
    private PredicateTree pTree;
    public String generateIndepMatrix(){
    	parameters.add("_p");
    	parameters.add("_q");
    	parameters.add("_a");
    	parameters.add("_b");
    	
    	if(isIndepMatrixAlreadyDefined())
    	{
    		System.out.println("User-defined IndepMatrix definition already exists.");
    		return "";
    	}
    	
    	boolean dependencyFound = false;
    	//String indepMatrixPredicate = "IndepMatrix(" + parameters.get(0) + ", " + parameters.get(1) + ") == [ " + parameters.get(2) + " \\in {";
    	String indepMatrixPredicate = "IndepMatrix(" + parameters.get(0) + ", " + parameters.get(1) + ", " + parameters.get(2) + ", " + parameters.get(3) + ") == ";
    	String actionNames = "";
    	String predicates = "";
    	
    	for (Map.Entry<String, ActionStructure> entryA:actions.entrySet()) 
    	{
            String actionA = entryA.getKey();
            ActionStructure statementsA = entryA.getValue();

            //Check if its action then add the name of action in the list
            if(!statementsA.nextPC.equals(""))
            {
            	actionNames += "\"" + actionA + "\", " ;
            }
            else
            	continue;
            
            for (Map.Entry<String, ActionStructure> entryB:actions.entrySet()) 
            {
                String actionB = entryB.getKey();
                ActionStructure statementsB = entryB.getValue();

                if(statementsB.nextPC.equals(""))
                	continue;
                
                //To avoid duplication of predicates
                if(actionNames.contains("\"" + actionB + "\"") && !actionA.equals(actionB))
                	continue;
                
                //String result = compareBlocks(actionA, actionB, statementsA, statementsB);
                
                pTree = new PredicateTree();
                compareBlocks(statementsA.statements, statementsB.statements, "(" + parameters.get(2) + " = \"" + actionA + "\" /\\ " + parameters.get(3) + " = \"" + actionB + "\" ");

                String predicate = "";
                //predicate = pTree.generateTree();
                //System.out.println("Predicate for " + actionA + " and " + actionB + "******************************************" + "\n" + predicate);
                                
                pTree.fixTree(parameters);
                //predicate = pTree.generateTree();
                //System.out.println("After fixing above tree******************************************\n" + predicate);

                pTree.normalizeTree();
                predicate = pTree.generateTree();
                //System.out.println("After nomalizing the tree******************************************\n" + predicate);

                if(predicate.startsWith("/\\ FALSE"))
                {
                	dependencyFound = true;
                	continue;
                }
                
                //listOfPredicates = simplifyPredicate(listOfPredicates);
                
                String preStr = "\n [] (" + parameters.get(2) + " = \"" + actionA + "\" /\\ " + parameters.get(3) + " = \"" + actionB + "\") -> ";
                String spaces = getSpaces(preStr.length()-1);
                boolean flagFirstPredicateAdded = false;
                predicates += preStr + "( \n" + predicate + ")";
            }            
        }
    	if(!predicates.equals(""))
    	{
    		//predicates = predicates.substring(0, predicates.length()-4);
    	}
    	else if(dependencyFound)
    	{
    		predicates = "FALSE";
    	}
    	else
    		predicates = "TRUE";
    	actionNames = actionNames.substring(0, actionNames.length()-2);
    	
    	if(predicates.startsWith("\n []"))
    	{
    		predicates = predicates.substring(4, predicates.length());
    		predicates = "\n   " + predicates;
    	}
    	
    	
    	indepMatrixPredicate += "\n CASE " + predicates + "\n [] OTHER -> FALSE";
    	//System.out.println(indepMatrixPredicate);
    	return indepMatrixPredicate + "\n\n";
    }
    


    /**Not using any more because we dont have any disjunctions
     * This function adds a conjunction around branch predicates. 
     * 
     * @param temp1
     * @return
     */
    private ArrayList<String> addConj(ArrayList<String> temp1)
    {

    	ArrayList<String> temp = new ArrayList<String>();

    	String spaces = "     ";
    	boolean flag = false;
    	for(int i=0;i<temp1.size(); i++)
    	{
    		if(temp1.get(i).startsWith(" \\/ ") && !flag)
    		{
    			if(i == temp1.size()-1)
    			{
    				temp.add(i, " /\\ (" + temp1.get(i) + ")");
    			}
    			else
    			{
    				temp.add(i, " /\\ (" + temp1.get(i));
    			}
    			flag = true;
    		}
    		else if(i == temp1.size()-1 && flag)
    			temp.add(i, spaces + temp1.get(i) + ")");
    		else if (flag)
    			temp.add(i, spaces + temp1.get(i));
    		else
    			temp.add(i, temp1.get(i));
    	}
		return temp;
    }
}
