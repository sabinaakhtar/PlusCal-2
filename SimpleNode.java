

public class SimpleNode implements Node {
  protected Node parent;
  protected Node[] children;
  protected int id;
  protected pcal parser;
  Token firstToken, lastToken;
  boolean AlreadyNormalized;
  boolean blockNotContainsLabel;

  public SimpleNode(int i) {
    id = i;
	AlreadyNormalized = false;
	blockNotContainsLabel = false;
  }

  public SimpleNode(pcal p, int i) {
    this(i);
    parser = p;
	AlreadyNormalized = false;
  }

  public void jjtOpen() {
  }

  public void jjtClose() {
  }
  
  public void jjtSetParent(Node n) { parent = n; }
  public Node jjtGetParent() { return parent; }

  public void jjtAddChild(Node n, int i) {
    if (children == null) {
      children = new Node[i + 1];
    } else if (i >= children.length) {
      Node c[] = new Node[i + 1];
      System.arraycopy(children, 0, c, 0, children.length);
      children = c;
    }
    children[i] = n;
  }

  public Node jjtGetChild(int i) {
    return children[i];
  }

  public int jjtGetNumChildren() {
    return (children == null) ? 0 : children.length;
  }

   /* if name is set, it will override the default value in toString */   
   private String name;   
   public void setName(String n) {
      name = n;
   }

  /* You can override these two methods in subclasses of SimpleNode to
     customize the way the node appears when the tree is dumped.  If
     your output uses more than one line you should override
     toString(String), otherwise overriding toString() is probably all
     you need to do. */

   public String toString() { 
      if (name!=null) {
	 return name;
      } else {
	 return pcalTreeConstants.jjtNodeName[id]; 
      }
   }
   
  public String toString(String prefix) { return prefix + toString(); }

  /* Override this method if you want to customize how the node dumps
     out its children. */

  public void dump(String prefix) {
    System.out.println(toString(prefix));
    if (children != null) {
      for (int i = 0; i < children.length; ++i) {
	SimpleNode n = (SimpleNode)children[i];
	if (n != null) {
	  n.dump(prefix + " ");
	}
      }
    }
  }
  
  //---------------------Pcal specific code-----------------------------//
  public void jjtChangeName(String newName) { pcalTreeConstants.jjtNodeName[id] = newName;}
  public void jjtRemoveChild(int i)
  {
    if (children == null || i >= children.length) {
      ;
    }
    else{
        
        Node[] childrenCopy = new Node[children.length - 1];
        int positionToCopy = 0;
        //children = null;
        for(int j=0;j<children.length;j++)
        {
            if(i!=j)
            {
                childrenCopy[positionToCopy] = children[j];
                positionToCopy++;
            }
        }
        children = childrenCopy;
/*
        System.out.println("dumping children....");
        children[0].dump("");

        System.out.println("dumping childrencopy....");
        childrenCopy[0].dump("");

        System.out.println("dumping done....");
*/
    }
  }
  public String reproduceText() 
	{
		StringBuffer text = new StringBuffer();
		Token t = firstToken;
                String currText = "", preText = "";
		while ( t!=null ) {
                        currText = t.image;
                        if(preText.compareTo("") != 0)
                        {
                            if(isChar(preText.charAt(preText.length()-1)) && isChar(currText.charAt(0)))
                                text.append(" " + t.image);
                            else
                                text.append(t.image);
                        }
                        else
                            text.append(t.image);
                        if(t == lastToken)
                            break;
                        preText = t.image;
                        t=t.next;
		}
		return text.toString();
	}
  public boolean isChar(char c)
  {
      String s = Character.toString(c);
    String characters = "abcdefghijklmnopqrstuvwxyz";
    String UCCharacters = characters.toUpperCase();
    if(characters.contains(s) || UCCharacters.contains(s))
        return true;
    else
        return false;
  }
  public String reproduceOperator()
  {
    return firstToken.toString();
  }
  
  public String getTextAt(int pos)
  {
      try
      {
          Token t = firstToken;
          for(int i=1;i<pos;i++)
              t = t.next;
          return t.toString();
      }
      catch(Exception e)
      {}
      return "";
  }
  public String getLineAndColumnNumber(int pos)
  {
    //Token t = firstToken;
    //return "line " + firstToken.beginLine + ", column " + firstToken.beginColumn;
      try
      {
          Token t = firstToken;
          for(int i=1;i<pos;i++)
              t = t.next;
          return "line " + t.beginLine + ", column " + t.beginColumn;
      }
      catch(Exception e)
      {}
      return "";
  }
  public String getLineNumber()
  {
	  if(firstToken != null)
		  return "line " + firstToken.beginLine;
	  else
		  System.out.println("Warning: firstToken null");
	  return "line null";
  }
  public void setToken(String str)
  {
	  if(str.equals("/\\"))
	  {
		  firstToken = new Token(pcalConstants.INFIX, str);
	  }
	  else if(str.equals("~"))
	  {
		  firstToken = new Token(pcalConstants.LNOT, str);
	  } 
	  else if(str.equals("TRUE"))
	  {
		  firstToken = new Token(pcalConstants.TRUE, str);
	  } 
	  else
	  {
		  System.out.println("Unable to create new token.");
	  }
  }
  
  public void Normalized()
  {
  	AlreadyNormalized = true;
  }
  public boolean isNormalized()
  {
	  return AlreadyNormalized;
  } 
  
	  public void BlockNotContainsLabel()
	  {
	  	blockNotContainsLabel = true;
	  }
	  public boolean doesBlockNotContainsLabel()
	  {
		  return blockNotContainsLabel;
	  } 
  public int jjtGetChildNumber(Node child)
  {
	  
      for(int j=0;j<children.length;j++)
      {
		  if(child == children[j])
			  return j;
      }
	  
	  return -1;
  }  
  
}


