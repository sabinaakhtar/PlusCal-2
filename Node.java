

/* All AST nodes must implement this interface.  It provides basic
   machinery for constructing the parent and child relationships
   between nodes. */

public interface Node {

  /** This method is called after the node has been made the current
    node.  It indicates that child nodes can now be added to it. */
  public void jjtOpen();

  /** This method is called after all the child nodes have been
    added. */
  public void jjtClose();

  /** This pair of methods are used to inform the node of its
    parent. */
  public void jjtSetParent(Node n);
  public Node jjtGetParent();

  /** This method tells the node to add its argument to the node's
    list of children.  */
  public void jjtAddChild(Node n, int i);

  /** This method returns a child node.  The children are numbered
     from zero, left to right. */
  public Node jjtGetChild(int i);

  /** Return the number of children the node has. */
  public int jjtGetNumChildren();
  
  //----------------pcal specific code------------------//
  
  public String reproduceText();
  public String reproduceOperator();
  public String getTextAt(int pos);
  public void dump(String prefix);
  public void jjtRemoveChild(int i);
  public void jjtChangeName(String newName);
  public String getLineAndColumnNumber(int pos);
  public String getLineNumber();
  public void setName(String name);
  public void setToken(String str);
  public void Normalized();
  public boolean isNormalized();
  public void BlockNotContainsLabel();
  public boolean doesBlockNotContainsLabel();
  public int jjtGetChildNumber(Node child);
}
