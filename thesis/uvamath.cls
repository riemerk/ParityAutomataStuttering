\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{uvamath}[2017/10/27 0.4 Bachelor Wiskunde LaTeX document class]
\LoadClassWithOptions{scrreprt}
\RequirePackage{graphicx}

\DeclareOption{english}{
% English values for translatable constant text
\def\supervisortextsingular{Supervisor}
\def\supervisortextplural{Supervisors}
\def\titletext{Title}
\def\authortextsingular{Author}
\def\authortextplural{Authors}
\def\datetext{End date}
\def\secondgradertextsingular{Second grader}
\def\secondgradertextplural{Second graders}
\def\thesistext{Bachelor thesis Mathematics}
\def\thesisWNtext{Bachelor thesis Mathematics and Physics \& Astronomy}
\def\thesisWItext{Bachelor thesis Mathematics and Computer Science}
\def\secondyearprojecttext{Project report Mathematics year 2}
\def\compalgtext{Computer algebra-\LaTeX}
\def\kdvitext{Korteweg-de Vries Institute for Mathematics}
\def\uvatext{University of Amsterdam}
\def\fnwitext{Faculty of Sciences}
\def\illctext{Institute for Logic, Language and Computation}
}


% Default values for translatable constant text
\def\supervisortextsingular{Begeleiding}
\def\supervisortextplural{Begeleiding}
\def\titletext{Titel}
\def\authortextsingular{Auteur}
\def\authortextplural{Auteurs}
\def\datetext{Einddatum}
\def\secondgradertextsingular{Tweede beoordelaar}
\def\secondgradertextplural{Tweede beoordelaars}
\def\thesistext{Bachelorscriptie Wiskunde}
\def\thesisWNtext{Bachelorscriptie Wiskunde en Natuur- \& Sterrenkunde}
\def\thesisWItext{Bachelorscriptie Wiskunde en Informatica}
\def\secondyearprojecttext{Projectverslag Wiskunde jaar 2}
\def\compalgtext{Computeralgebra-\LaTeX}
\def\kdvitext{Korteweg-de Vries Instituut voor Wiskunde}
\def\uvatext{Universiteit van Amsterdam}
\def\fnwitext{Faculteit der Natuurwetenschappen, Wiskunde en Informatica}
\def\ioptext{Institute of Physics}
\def\illctext{Instituut voor Logica, Taal en Computatie}


% Variable text commands
\def\institute#1{\gdef\@institute{#1}}
\def\instituteaddress#1{\gdef\@instituteaddress{#1}}
\def\coverimage#1{\gdef\@coverimage{#1}}
\def\supervisors#1{\gdef\@supervisors{#1}}
\def\secondgrader#1{\gdef\@secondgrader{#1}}

% Options for various projects

\DeclareOption{complatex}{
    \def\whichprojecttext{\compalgtext}
    \institute{
    \kdvitext \\\smallskip
    \fnwitext\\\smallskip
    \uvatext\\\bigskip
%     \includegraphics[width=0.070\hsize]{uvalogo.png}
    }

    \instituteaddress{\kdvitext\\
    \uvatext\\
    Science Park 904, 1098 XH Amsterdam\\
    \url{http://www.kdvi.uva.nl}{}
    }
}

\DeclareOption{tweedejaarsproject}{
    \def\whichprojecttext{\secondyearprojecttext}
    \institute{
    \kdvitext \\\smallskip
    \fnwitext\\\smallskip
    \uvatext\\\bigskip
%     \includegraphics[width=0.070\hsize]{uvalogo}
    }

    \instituteaddress{\kdvitext\\
    \uvatext\\
    Science Park 904, 1098 XH Amsterdam\\
    \url{http://www.kdvi.uva.nl}{}
    }
}

\DeclareOption{bachelorscriptie}{
    \def\whichprojecttext{\thesistext}
    \institute{
    \kdvitext \\\smallskip
    \fnwitext\\\smallskip
    \uvatext\\\bigskip
%     \includegraphics[width=0.070\hsize]{uvalogo}
    }

    \instituteaddress{\kdvitext\\
    \uvatext\\
    Science Park 904, 1098 XH Amsterdam\\
    \url{http://www.kdvi.uva.nl}{}
    }
}

\DeclareOption{dubaWN}{
    \def\whichprojecttext{\thesisWNtext}
    \institute{
    \ioptext \\\smallskip
    \kdvitext \\\smallskip
    \fnwitext\\\smallskip
    \uvatext\\\bigskip
%     \includegraphics[width=0.070\hsize]{uvalogo}
    }

    \instituteaddress{\ioptext\\
    \uvatext\\
    Science Park 904, 1098 XH Amsterdam\\
    \url{http://www.iop.uva.nl}{} \bigskip \\
    \kdvitext\\
    \uvatext\\
    Science Park 904, 1098 XH Amsterdam\\
    \url{http://www.kdvi.uva.nl}{}
    }
}

\DeclareOption{dubaWI}{
    \def\whichprojecttext{\thesisWItext}
    \institute{
    \illctext \\\smallskip
    \kdvitext \\\smallskip
    \fnwitext\\\smallskip
    \uvatext\\\bigskip
    \includegraphics[width=0.085\hsize]{uvalogo}\\\bigskip
    \includegraphics{illclogo}
    }

    \instituteaddress{\illctext\\
    \uvatext\\
    Science Park 107, 1098 XG Amsterdam\\
    \url{http://www.illc.uva.nl}{}
    \bigskip\\
    \kdvitext\\
    \uvatext\\
    Science Park 107, 1098 XG Amsterdam\\
    \url{http://www.kdvi.uva.nl}{}
    }
}

%\DeclareOption*{}
\ProcessOptions%\relax

\setkomafont{disposition}{\bfseries}
%\RequirePackage[a4paper]{geometry}

% Default values for variable text
\coverimage{}
\supervisors{\relax}
\secondgrader{\relax}


% Author command
\newcounter{authors}
\def\@authordetails{}
\def\@authors{}
\renewcommand\author[2][\relax]{
    \ifnum\value{authors}>0\relax
        \addtocounter{authors}{1}
        \xdef\@authors{\@authors, #2}
        \protected@xdef\@authordetails{\@authordetails\protect{\\} \indent #2\if#1\relax\else{, #1}\fi}
    \else
        \addtocounter{authors}{1}
        \gdef\@authors{#2}
        \gdef\@authordetails{#2, #1}
    \fi
}

\newcounter{supervisornum}
\def\@supervisordetails{}
\def\@supervisors{}
\renewcommand\supervisors[2][\relax]{
    \ifnum\value{supervisornum}>0\relax
        \addtocounter{supervisornum}{1}
        \xdef\@supervisors{\@supervisors, #2}
        \protected@xdef\@supervisordetails{\@supervisordetails #2\if#1\relax\else{, #1}\fi}
    \else
        \addtocounter{supervisornum}{1}
        \gdef\@supervisors{#2}
        \gdef\@supervisordetails{#2, #1}
    \fi
}

\newcounter{secondgradernum}
\def\@secondgraderdetails{}
\def\@secondgrader{}
\renewcommand\secondgrader[2][\relax]{
    \ifnum\value{secondgradernum}>0\relax
        \addtocounter{secondgradernum}{1}
        \xdef\@secondgraders{\@secondgrader, #2}
        \protected@xdef\@secondgraderdetails{\@secondgraderdetails #2\if#1\relax\else{, #1}\fi}
    \else
        \addtocounter{secondgradernum}{1}
        \gdef\@secondgrader{#2}
        \gdef\@secondgraderdetails{#2, #1}
    \fi
}



% Maketitle command
\renewcommand{\maketitle}{
\pagestyle{empty}
\vspace*{30pt}
{\centering
{\LARGE \textbf{\bfseries \@title}\par}\bigskip
{\Large \@authors
\par}\bigskip
{\Large \@date\par}\bigskip\bigskip
{\large \whichprojecttext\par}\medskip
\if\@supervisors\relax\else {\large\supervisortextplural: \@supervisors\par}\bigskip\fi
\vspace{\stretch{1}}
\@coverimage
\vspace{\stretch{1}}

\@institute

\vspace{-70pt}
}
\newpage
\pagestyle{plain}
}

% Abstract and info page
\renewenvironment{abstract}{\section*{\abstractname}}{
\vfill
%\section*{Gegevens}
\noindent
\titletext: \@title\\
\ifnum\value{authors} < 2%
\authortextsingular: \@authordetails\\
\else
\authortextplural:\\ \indent\@authordetails\\
\fi
%
\ifnum\value{supervisornum} < 2%
\supervisortextsingular: \@supervisordetails\\
\else
\supervisortextplural: \@supervisordetails\\
\fi
%
\if\@secondgrader\relax\else
\ifnum\value{secondgradernum} < 2%
\secondgradertextsingular: \@secondgraderdetails\\
\else
\secondgradertextplural: \@secondgraderdetails\\
\fi \fi
\datetext: \@date

\bigskip\noindent
\@instituteaddress
\newpage
}



\endinput
