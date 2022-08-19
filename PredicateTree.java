import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;



public class PredicateTree {
    
	class Tree{
	    public String type;
	    public int index;
	    public String code;
	    public LinkedHashMap<String, String> letInStatements;
	    
	    ArrayList<Tree> children;
	    Tree parent;
	    
	    
	
	    //Constructor
	    public Tree(String t, int i, Tree p){
	    this.type = t;
	    this.index = i;
	    this.parent = p;
	    this.code = "";
		this.letInStatements = new LinkedHashMap<String,String>();
		this.children = new ArrayList<PredicateTree.Tree>();
	    }	
	    public void setCode(String c){
	    	this.code = c;
	    	}

    }
	
	ArrayList<String> conditions;
	ArrayList<String> predicates;
	Tree tree;
	Tree currentNode;
    
	public PredicateTree()
    {
		conditions = new ArrayList<String>();
		predicates = new ArrayList<String>();
		tree = new Tree("root", -1, null);
    	currentNode = tree;
    }
	public void setLetInStatements(LinkedHashMap<String, String> sts)
	{
		try
		{
			if(sts != null)
			{
				Set<Entry<String, String>> entryset = sts.entrySet();
				Entry<String, String>[] entry = new Entry[entryset.size()]; 
				entryset.toArray(entry);

				for (int i = 0;i<entry.length;i++) 
				{
					String key = entry[i].getKey();
					String value = entry[i].getValue();
					if(currentNode.letInStatements.containsKey(key))
					{
						String preVal = currentNode.letInStatements.get(key);
						if(!preVal.equals(value))
						{
							String newVal = value.substring(value.indexOf("EXCEPT")+6, value.length()-1);
							newVal = preVal.substring(0, preVal.length()-1) + ","+ newVal + "]";
							currentNode.letInStatements.put(key, newVal);
						}
					}
					else
					{
						currentNode.letInStatements.put(key, value);
					}
					
					
				}
				
			}
		}
		catch(Exception e)
		{
			System.out.println("Bug in PredicateTree.java. Exception:" + e);
		}
	}
    public void addPredicate(String p)
    {
    	try
    	{
	    	if(!predicates.contains(p))
	    	{
	    		predicates.add(p);
	    	}
	    	Tree newNode = new Tree("p", predicates.indexOf(p), currentNode);
	    	currentNode.children.add(newNode);
    	}
    	catch(Exception e)
    	{
    		System.out.println("Bug in PredicateTree.java. Exception:" + e);
    	}
    }
    public void addCondition(String c)
    {
		try
		{
	    	if(!conditions.contains(c))
	    	{
	    		conditions.add(c);
	    	}
	    	Tree newNode = new Tree("c", conditions.indexOf(c), currentNode);
	    	currentNode.children.add(newNode);
	    	currentNode = newNode;
		}
		catch(Exception e)
		{
			System.out.println("Bug in PredicateTree.java. Exception:" + e);
		}
    }
    public void cutBranch()
    {
    	currentNode.children.clear();
    	this.addPredicate("FALSE");
    	
    }
    public void close()
    {
    	currentNode = currentNode.parent;
    }
    

    //----------------------------------------------------Tree Normalization
    public void normalizeTree()
    {
    	if(tree.children.size() > 0)
    	{
    		this.normalize(this.tree);
    	}
    }
    private void normalize(Tree tree)
    {
    	HashMap<String, ArrayList<Integer>> codes = new HashMap<String, ArrayList<Integer>>();
    	
    	for(int i=0;i<tree.children.size();i++)
    	{
    		Tree child = tree.children.get(i);
    		if(child.type.equals("p"))
    		{
    			child.code = "P" + child.index;
    			if(codes.containsKey(child.code))
    			{
    				//System.out.println("found similar predicates");
    				tree.children.remove(i);
    				i--;
    			}
    			else
    			{
    				ArrayList<Integer> value = new ArrayList<Integer>();
    				value.add(i);
    				codes.put(child.code, value);
        			tree.code += "P" + child.index;
    			}
    		}
    		else
    		{
    			normalize(child);
    			//System.out.println(child.code);
    			if(codes.containsKey(child.code))
    			{
    				//check if the conditions are negation of each other
    				boolean result = fixIfItsNegationOfOther(codes.get(child.code), tree, i);
    				if(result)
    				{
    					i--;
    					continue;
    				}
    				else
    				{
        				ArrayList<Integer> value = codes.get(child.code);
        				value.add(i);
        				codes.put(child.code, value);
    				}
    			}
    			else
    			{
    				ArrayList<Integer> value = new ArrayList<Integer>();
    				value.add(i);
    				codes.put(child.code, value);
    			}
    			tree.code += "C" + child.index;
    		}
    	}
    }
    
    private boolean fixIfItsNegationOfOther(ArrayList<Integer> list, Tree tree, int i)
    {
    	Tree child = tree.children.get(i);
		String condition2 = conditions.get(child.index);
		boolean flag = false;
		for(int k = 0; k < list.size();k++)
		{
			int index = list.get(k);
			Tree temp = tree.children.get(index);
			String condition1 = conditions.get(temp.index);
			if(condition1.startsWith("~("))
			{
				condition1 = condition1.substring(2, condition1.length()-1);
				if(condition1.equals(condition2))
				{
					removeSimilarBranches(tree, i, index);
					flag = true;
				}
			}
			else if(condition2.startsWith("~("))
			{
				condition2 = condition2.substring(2, condition2.length()-1);
				if(condition1.equals(condition2))
				{
					removeSimilarBranches(tree, i, index);
					flag = true;
				}
			}
			else if(condition1.equals(condition2))
			{
				tree.children.remove(i);
				flag = true;
			}
				
		}
		return flag;
    }
    private void removeSimilarBranches(Tree tree, int index1, int index2)
    {
    	tree.children.remove(index1);
    	Tree temp = tree.children.remove(index2);
    	
    	
		tree.children.addAll(temp.children);
		tree.code = temp.code;

    	/*
    	if(tree.children.size() > 2)
    	{
    		System.out.println("Branch with more than 2 children found.\n Unable to remove similar branches.");
    	}
    	else
    	{
    		tree.children.clear();
    		tree.children = temp.children;
    		tree.code = temp.code;
    	}*/
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
    //--------------------------------------Tree display-------------------------------------
    public String generateTree()
    {
    	String result = "";
    	int tab = 6;
    	if(this.tree.children.size() > 0)
    	{
    		result = genletin(this.tree, 0);
    		if(!result.equals(""))
    		{
    			tab += 3;
    		}
    		for(int i=0;i<this.tree.children.size();i++)
    		{
    			result += generate(this.tree.children.get(i), tab);
    		}
    	}
    	result = result.substring(0, result.length()-1);
    	return result;
    }
    private String generate(Tree t, int tab)
    {
    	String result = "";
    	if(t.type.equals("p"))
    	{
    		result = getSpaces(tab) + "/\\ " +predicates.get(t.index) + "\n";
    	}
    	else if(t.type.equals("c"))
    	{

    		String cond = getSpaces(tab) + "/\\ " + conditions.get(t.index) + " => ";
        	tab += 3;
    		result = cond + "\n";
    		int preLen = result.length();
    		result += genletin(t, tab);
    		if(preLen < result.length())
    			tab+=3;

    		for(int i=0;i<t.children.size();i++)
    		{
    			result += generate(t.children.get(i), tab);
    		}
    	}
    	return result;
    }
    
    private String genletin(Tree t, int tab)
    {
    	String result = "";
		Set<Entry<String, String>> entryset = t.letInStatements.entrySet();
		Entry<String, String>[] entry = new Entry[entryset.size()]; 
		entryset.toArray(entry);

		for (int i = 0;i<entry.length;i++) 
		{
			String key = entry[i].getKey();
			String value = entry[i].getValue();
			if(i == 0)
				result += getSpaces(tab) + "/\\ LET " + key + " == " + value + " IN \n" ;
			else
				result += getSpaces(tab) + "   LET " + key + " == " + value + " IN \n";
		}
		return result;
    }
    //************************************Fix Letin Statements
    
    public void fixTree(ArrayList<String> parameters)
    {
    	fixLETINs(this.tree, parameters, null);
    }
    
    //------------------------------------
    
    private Map<String, String> fixVariableNames(Tree t, ArrayList<String> parameters, Map<String, String> lastKeyListOrg)
    {
    	LinkedHashMap<String, String> list = t.letInStatements;
    	LinkedHashMap<String, String> newListOfStatements = new LinkedHashMap<String, String>();
    	Map<String, String> lastKeyList = new LinkedHashMap<String, String>();
    	if(lastKeyListOrg != null)
    	{
    		lastKeyList.putAll(lastKeyListOrg);
    	}
    	
		Set<Entry<String, String>> entryset = list.entrySet();
		Entry<String, String>[] entry = new Entry[entryset.size()]; 
		entryset.toArray(entry);
		

		String lastKey = "";

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
				key = "_" + newVar;
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
			newListOfStatements.put(key, value);		
		}
		t.letInStatements = newListOfStatements;
		return lastKeyList;
    }
    
    private Map<String, String> mergeLastKeyList(Map<String, String> list1, Map<String, String> list2)
    {
    	if(list2 == null)
    		return list1;
    	
    	Map<String, String> newlist = new LinkedHashMap<String, String>();
    	for (Map.Entry<String, String> entry: list2.entrySet()){
            String key = entry.getKey();
            String value = entry.getValue();
            
            newlist = addVartoLastKeyList(key, list1, true);
    	}
    	return newlist;
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
    /**
     * It replaces the variable names in a given expression with a specified variable
     * @param completeStr The expression
     * @param searchStr The variable to be changed
     * @param replacementStr The new variable
     * @return The new expression
     */
    private String replaceVariableNames(String completeStr, String searchStr, String replacementStr)
    {
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
    
    //------------------------------------
    
    private void fixLETINs(Tree tree, ArrayList<String> parameters, Map<String, String> lastKeyList)
    {
    	Map<String, String> lastKeyList1 = null;
    	String expression = "";
    	String nexpression = "";
    	
    	if(tree.type.equals("p"))
    	{
    		expression = predicates.get(tree.index);
    		nexpression = searchAndReplace(expression, lastKeyList);
    		if(predicates.contains(nexpression))
    		{
    			tree.index = predicates.indexOf(nexpression);
    		}
    		else
    		{
    			predicates.set(tree.index, nexpression);
    		}
    	}
    	else if(tree.type.equals("c"))
    	{
    		expression = conditions.get(tree.index);
    		nexpression = searchAndReplace(expression, lastKeyList);
    		if(conditions.contains(nexpression))
    		{
    			tree.index = conditions.indexOf(nexpression);
    		}
    		else
    		{
    			conditions.set(tree.index, nexpression);
    		}
    	}
    	
    	if(!tree.letInStatements.isEmpty())
    	{
    		tree.letInStatements = this.fixList(tree, tree.letInStatements);

    		lastKeyList = this.fixVariableNames(tree, parameters, lastKeyList);
    		lastKeyList = mergeLastKeyList(lastKeyList, lastKeyList1);
    	}
    	
    	for(int i = 0;i< tree.children.size();i++)
    	{
    		Tree child = tree.children.get(i);
    		fixLETINs(child, parameters, lastKeyList);
    	}
    }
    
    private LinkedHashMap<String, String> fixList(Tree node, LinkedHashMap<String, String> list)
    {
    	LinkedHashMap<String, String> finalList = new LinkedHashMap<String, String>();
		LinkedHashMap<String, String> list1;
		LinkedHashMap<String, String> list2;
		
    	for(int i=0; i< node.children.size(); i++)
    	{
    		Tree child = node.children.get(i);

    		if(child.type.equals("p"))
    		{
    			list1 = correctList(predicates.get(child.index), list);
    			finalList.putAll(list1);
    		}
    		else
    		{
    			list1 = correctList(conditions.get(child.index), list);
    			list2 = fixList(child, list);
    			finalList.putAll(list1);
    			finalList.putAll(list2);
    		}
    	}
    	return finalList;
    }

    private LinkedHashMap<String, String> correctList(String expression, LinkedHashMap<String, String> list)
    {
    	String LETstatements = "";
		boolean flag = true;
		String temp = expression;
		String varsToIgnore = "";

		LinkedHashMap<String, String> tempMap = new LinkedHashMap<String, String>();
		while(flag)
		{
			flag = false;
						
			Set<Entry<String, String>> entryset = list.entrySet();
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
		return tempMap;
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
    
}
