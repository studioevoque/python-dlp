<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet
    xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
    xmlns:sr="http://www.w3.org/2005/sparql-results#"
    xmlns="http://www.w3.org/1999/xhtml"
    version="1.0">
  <xsl:output indent="yes"/>

  <xsl:param name="min-result" select="1"/>
  <xsl:param name="max-result" select="100"/>

  <xsl:template match="node()|@*"/>

  <xsl:template match="/">
    <html>
      <head>
        <title>SPARQL results</title>
        <style type="text/css">
span.uri, span.datatype
{
  font-family: monospace;
}

span.bnode
{
  font-style: italic;
}

th
{
  background-color: #eff;
}

td
{
  padding: 4px;
}

td.number
{
  background-color: #efefef;
  text-align: center;
  font-weight: bold;
}

tr:hover, tr.even:hover
{
  background-color: #efe;
}

span.qname
{
  font-size: smaller;
}

tr.even
{
  background-color: #eaefff;
}
        </style>
      </head>

      <body>
        <h1>SPARQL results</h1>

        <p>In the following results, the <code>xsd</code> prefix is bound to
        the uri <code>http://www.w3.org/2001/XMLSchema#</code>.</p>

        <p>URIs and Blank nodes in the results are linkable.  Clicking on them will take 
        you to the triple browser anchored on the URI or blank node that was clicked</p>

        <xsl:apply-templates/>
      </body>
    </html>
  </xsl:template>

  <xsl:template match="sr:sparql">
    <table>
      <tr>
        <th>Result number</th>
        <xsl:apply-templates select="sr:head/sr:variable" mode="header"/>
      </tr>
      
      <xsl:choose>
        <xsl:when test="$max-result &gt; 0 and
                        count(sr:results/sr:result) &gt;
                          ($max-result - $min-result + 1)">
          <xsl:apply-templates select="sr:results/sr:result[
            position() &gt;= $min-result and
            position() &lt;= $max-result]"/>
        </xsl:when>
        <xsl:otherwise>
          <xsl:apply-templates select="sr:results/sr:result"/>
        </xsl:otherwise>
      </xsl:choose>
    </table>
    <xsl:if test="$max-result &gt; 0 and count(sr:results/sr:result) &gt;
                      ($max-result - $min-result + 1)">
      <p>Only results <xsl:value-of select="$min-result"/> through
      <xsl:value-of select="$max-result"/> are displayed above.  (There are
      <xsl:value-of select="count(sr:results/sr:result)"/> total
      results.)</p>
    </xsl:if>
  </xsl:template>

  <xsl:template match="sr:variable" mode="header">
    <th><xsl:value-of select="@name"/></th>
  </xsl:template>

  <xsl:template match="sr:results/sr:result">
    <xsl:variable name="resultPos" select="position()"/>
    <tr>
      <xsl:choose>
        <xsl:when test="count(preceding-sibling::sr:result) mod 2 = 0">
          <xsl:attribute name="class">even</xsl:attribute>
        </xsl:when>
        <xsl:otherwise>
          <xsl:attribute name="class">odd</xsl:attribute>
        </xsl:otherwise>
      </xsl:choose>
      <td class="number"><xsl:number value="$resultPos + $min-result - 1"/></td>
      
      <xsl:for-each select="/sr:sparql/sr:head/sr:variable/@name">
        <xsl:variable name="varName" select="."/>
        <xsl:choose>
          <xsl:when test="/sr:sparql/sr:results/sr:result[$resultPos]/sr:binding[@name = $varName]">
            <xsl:apply-templates select="/sr:sparql/sr:results/sr:result[$resultPos]/sr:binding[@name = $varName]"/>    
          </xsl:when>
          <xsl:otherwise><td></td></xsl:otherwise>
        </xsl:choose>
      </xsl:for-each>
    </tr>
  </xsl:template>

  <xsl:template match="sr:binding">
    <xsl:variable name="pos" select="position()"/>
    <td>
      <xsl:choose>
        <xsl:when test="count(preceding-sibling::sr:binding) mod 2 = 0">
          <xsl:attribute name="class">even</xsl:attribute>
        </xsl:when>
        <xsl:otherwise>
          <xsl:attribute name="class">odd</xsl:attribute>
        </xsl:otherwise>
      </xsl:choose>
      <xsl:apply-templates/>        
    </td>
  </xsl:template>

  <xsl:template match="sr:binding/*">
    <xsl:choose>
      <xsl:when test="local-name() = 'uri'">
        <xsl:value-of select="."/>
        <!--a href="/browse?action=resource&amp;uri={.}"><xsl:value-of select="."/></a-->
      </xsl:when>
      <xsl:when test="local-name() = 'bnode'">
        <xsl:value-of select="."/>
        <!--a href="/browse?action=resource&amp;uri=_:{.}"><xsl:value-of select="."/></a-->
      </xsl:when>      
      <xsl:otherwise>
        <span class="{local-name()}"><xsl:value-of select="."/></span>
      </xsl:otherwise>
    </xsl:choose>
    
    <xsl:if test="@datatype">
      <xsl:text>^^</xsl:text>
      <xsl:choose>
        <xsl:when test="starts-with(@datatype, 'http://www.w3.org/2001/XMLSchema#')">
          <span class="qname">
            <xsl:text>xsd:</xsl:text>
            <xsl:value-of select="substring-after(@datatype,
              'http://www.w3.org/2001/XMLSchema#')"/>
          </span>
        </xsl:when>
        <xsl:otherwise>
          <xsl:text>&lt;</xsl:text>
          <span class="datatype"><xsl:value-of select="@datatype"/></span>
          <xsl:text>&gt;</xsl:text>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:if>
  </xsl:template>
</xsl:stylesheet>
