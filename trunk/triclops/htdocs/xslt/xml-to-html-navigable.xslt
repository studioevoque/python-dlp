<?xml version="1.0" encoding="UTF-8"?>
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" xmlns:sr="http://www.w3.org/2005/sparql-results#" xmlns="http://www.w3.org/1999/xhtml" version="1.0">
    <xsl:output indent="yes"/>
    <xsl:param name="min-result" select="1"/>
    <xsl:param name="max-result" select="100"/>

    <!-- 
        URL encoding, courtesy of Mike Brown: http://skew.org/xml/stylesheets/url-encode/
      -->
    <!-- Characters we'll support.
         We could add control chars 0-31 and 127-159, but we won't. -->
    <xsl:variable name="ascii"> !"#$%&amp;'()*+,-./0123456789:;&lt;=&gt;?@ABCDEFGHIJKLMNOPQRSTUVWXYZ[\]^_`abcdefghijklmnopqrstuvwxyz{|}~</xsl:variable>
    <xsl:variable name="latin1">&#160;&#161;&#162;&#163;&#164;&#165;&#166;&#167;&#168;&#169;&#170;&#171;&#172;&#173;&#174;&#175;&#176;&#177;&#178;&#179;&#180;&#181;&#182;&#183;&#184;&#185;&#186;&#187;&#188;&#189;&#190;&#191;&#192;&#193;&#194;&#195;&#196;&#197;&#198;&#199;&#200;&#201;&#202;&#203;&#204;&#205;&#206;&#207;&#208;&#209;&#210;&#211;&#212;&#213;&#214;&#215;&#216;&#217;&#218;&#219;&#220;&#221;&#222;&#223;&#224;&#225;&#226;&#227;&#228;&#229;&#230;&#231;&#232;&#233;&#234;&#235;&#236;&#237;&#238;&#239;&#240;&#241;&#242;&#243;&#244;&#245;&#246;&#247;&#248;&#249;&#250;&#251;&#252;&#253;&#254;&#255;</xsl:variable>

    <!-- Characters that usually don't need to be escaped -->
    <xsl:variable name="safe">!'()*-.0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz~</xsl:variable>
    <xsl:variable name="hex" >0123456789ABCDEF</xsl:variable>
    <xsl:template name="url-encode">
      <xsl:param name="str"/>   
      <xsl:if test="$str">
        <xsl:variable name="first-char" select="substring($str,1,1)"/>
        <xsl:choose>
          <xsl:when test="contains($safe,$first-char)">
            <xsl:value-of select="$first-char"/>
          </xsl:when>
          <xsl:otherwise>
            <xsl:variable name="codepoint">
              <xsl:choose>
                <xsl:when test="contains($ascii,$first-char)">
                  <xsl:value-of select="string-length(substring-before($ascii,$first-char)) + 32"/>
                </xsl:when>
                <xsl:when test="contains($latin1,$first-char)">
                  <xsl:value-of select="string-length(substring-before($latin1,$first-char)) + 160"/>
                </xsl:when>
                <xsl:otherwise>
                  <xsl:message terminate="no">Warning: string contains a character that is out of range! Substituting "?".</xsl:message>
                  <xsl:text>63</xsl:text>
                </xsl:otherwise>
              </xsl:choose>
            </xsl:variable>
          <xsl:variable name="hex-digit1" select="substring($hex,floor($codepoint div 16) + 1,1)"/>
          <xsl:variable name="hex-digit2" select="substring($hex,$codepoint mod 16 + 1,1)"/>
          <xsl:value-of select="concat('%',$hex-digit1,$hex-digit2)"/>
          </xsl:otherwise>
        </xsl:choose>
        <xsl:if test="string-length($str) &gt; 1">
          <xsl:call-template name="url-encode">
            <xsl:with-param name="str" select="substring($str,2)"/>
          </xsl:call-template>
        </xsl:if>
      </xsl:if>
    </xsl:template>
    
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
                <xsl:when test="$max-result &gt; 0 and                         count(sr:results/sr:result) &gt;                           ($max-result - $min-result + 1)">
                    <xsl:apply-templates select="sr:results/sr:result[             position() &gt;= $min-result and             position() &lt;= $max-result]"/>
                </xsl:when>
                <xsl:otherwise>
                    <xsl:apply-templates select="sr:results/sr:result"/>
                </xsl:otherwise>
            </xsl:choose>
        </table>
        <xsl:if test="$max-result &gt; 0 and count(sr:results/sr:result) &gt;                       ($max-result - $min-result + 1)">
            <p>Only results <xsl:value-of select="$min-result"/> through
      <xsl:value-of select="$max-result"/> are displayed above.  (There are
      <xsl:value-of select="count(sr:results/sr:result)"/> total
      results.)</p>
        </xsl:if>
    </xsl:template>
    <xsl:template match="sr:variable" mode="header">
        <th>
            <xsl:value-of select="@name"/>
        </th>
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
            <td class="number">
                <xsl:number value="$resultPos + $min-result - 1"/>
            </td>
            <xsl:for-each select="/sr:sparql/sr:head/sr:variable/@name">
                <xsl:variable name="varName" select="."/>
                <xsl:choose>
                    <xsl:when test="/sr:sparql/sr:results/sr:result[$resultPos]/sr:binding[@name = $varName]">
                        <xsl:apply-templates select="/sr:sparql/sr:results/sr:result[$resultPos]/sr:binding[@name = $varName]"/>
                    </xsl:when>
                    <xsl:otherwise>
                        <td/>
                    </xsl:otherwise>
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
    <xsl:template name="replace-text">
        <xsl:param name="text"/>
        <xsl:param name="replace"/>
        <xsl:param name="by"/>
        <xsl:choose>
            <xsl:when test="contains($text, $replace)">
                <xsl:value-of select="substring-before($text, $replace)"/>
                <xsl:value-of select="$by" disable-output-escaping="yes"/>
                <xsl:call-template name="replace-text">
                    <xsl:with-param name="text" select="substring-after($text, $replace)"/>
                    <xsl:with-param name="replace" select="$replace"/>
                    <xsl:with-param name="by" select="$by"/>
                </xsl:call-template>
            </xsl:when>
            <xsl:otherwise>
                <xsl:value-of select="$text"/>
            </xsl:otherwise>
        </xsl:choose>
    </xsl:template>
    <xsl:template match="sr:binding/*">
        <xsl:choose>
            <xsl:when test="local-name() = 'uri'">
                <!-- A URI Reference -->
                <xsl:choose>
                    <xsl:when test="string(../@name) = 'NAV_VAR'">
                        <!-- 
                solution variable indicated for use in navigation template
                -->
                        <xsl:choose>
                            <xsl:when test="?REPLACE?">
                                <!-- 
                        Create a $replaceUri variable for use, the URI has a pattern to be replaced
                      -->
                                <xsl:variable name="replacedUri">
                                    <xsl:call-template name="replace-text">
                                        <xsl:with-param name="text" select="."/>
                                        <xsl:with-param name="replace" select="'FROM'"/>
                                        <xsl:with-param name="by" select="'TO'"/>
                                    </xsl:call-template>
                                </xsl:variable>
                                <xsl:variable name="escapedReplacedUri">
                                    <xsl:call-template name="url-encode">
                                      <xsl:with-param name="str" select="$replacedUri"/>
                                    </xsl:call-template>
                                </xsl:variable>
                                <a href="?REPLACE_URI?">
                                    <xsl:value-of select="."/>
                                </a>
                            </xsl:when>
                            <xsl:otherwise>
                                <!-- No replacing of bound identifier, use in navigation template -->
                                <xsl:variable name="escapedUri">
                                    <xsl:call-template name="url-encode">
                                      <xsl:with-param name="str" select="."/>
                                    </xsl:call-template>
                                </xsl:variable>                                
                                <a href="?NO_REPLACE_URI?">
                                    <xsl:value-of select="."/>
                                </a>
                            </xsl:otherwise>
                        </xsl:choose>
                    </xsl:when>
                    <xsl:otherwise>
                        <!--  
                regular solution IRI binding.  Use 'Statements about a resource'
                query for follow-up (same for BNodes)
               -->
                        <a href="?GRAPH_NAVIGATE_URI?">
                            <xsl:value-of select="."/>
                        </a>
                    </xsl:otherwise>
                </xsl:choose>
            </xsl:when>
            <xsl:when test="local-name() = 'bnode'">
                <a href="?GRAPH_NAVIGATE_URI?">
                    <xsl:value-of select="."/>
                </a>
            </xsl:when>
            <xsl:otherwise>
                <span class="{local-name()}">
                    <xsl:value-of select="."/>
                </span>
            </xsl:otherwise>
        </xsl:choose>
        <xsl:if test="@datatype">
            <xsl:text>^^</xsl:text>
            <xsl:choose>
                <xsl:when test="starts-with(@datatype, 'http://www.w3.org/2001/XMLSchema#')">
                    <span class="qname">
                        <xsl:text>xsd:</xsl:text>
                        <xsl:value-of select="substring-after(@datatype,               'http://www.w3.org/2001/XMLSchema#')"/>
                    </span>
                </xsl:when>
                <xsl:otherwise>
                    <xsl:text>&lt;</xsl:text>
                    <span class="datatype">
                        <xsl:value-of select="@datatype"/>
                    </span>
                    <xsl:text>&gt;</xsl:text>
                </xsl:otherwise>
            </xsl:choose>
        </xsl:if>
    </xsl:template>
</xsl:stylesheet>
