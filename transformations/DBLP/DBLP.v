(** Imports Native *)
Require Import String.
Require Import Bool.
Require Import List.
Require Import PeanoNat.
Require Import EqNat.

(** Imports CoqTL *)
Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

(** Base types for elements *)
Record Record_t := { Record_ee : string ; Record_url : string ; Record_key : string ; Record_mdate : string }.
Scheme Equality for Record_t.


Record Article_t := { Article_title : string ; Article_fromPage : nat ; Article_toPage : nat ; Article_number : nat ; Article_volume : string ; Article_month : string ; Article_year : nat }.
Scheme Equality for Article_t.


Record Author_t := { Author_name : string }.
Scheme Equality for Author_t.


Record Journal_t := { Journal_name : string }.
Scheme Equality for Journal_t.


Record Book_t := { Book_title : string ; Book_year : nat ; Book_month : string ; Book_volume : nat ; Book_series : string ; Book_edition : nat ; Book_isbn : string }.
Scheme Equality for Book_t.


Record InCollection_t := { InCollection_title : string ; InCollection_bookTitle : string ; InCollection_year : nat ; InCollection_fromPage : nat ; InCollection_toPage : nat ; InCollection_month : string }.
Scheme Equality for InCollection_t.


Record InProceedings_t := { InProceedings_title : string ; InProceedings_bootitle : string ; InProceedings_year : nat ; InProceedings_fromPage : nat ; InProceedings_toPage : nat ; InProceedings_month : string }.
Scheme Equality for InProceedings_t.


Record MastersThesis_t := { MastersThesis_title : string ; MastersThesis_year : nat ; MastersThesis_month : string }.
Scheme Equality for MastersThesis_t.


Record Proceedings_t := { Proceedings_title : string ; Proceedings_year : nat ; Proceedings_month : string ; Proceedings_isbn : string }.
Scheme Equality for Proceedings_t.


Record PhDThesis_t := { PhDThesis_title : string ; PhDThesis_year : nat ; PhDThesis_month : string }.
Scheme Equality for PhDThesis_t.


Record Www_t := { Www_title : string ; Www_year : nat ; Www_month : string }.
Scheme Equality for Www_t.


Record Editor_t := { Editor_name : string }.
Scheme Equality for Editor_t.


Record Organization_t := { Organization_name : string }.
Scheme Equality for Organization_t.


Record Publisher_t := { Publisher_name : string ; Publisher_address : string }.
Scheme Equality for Publisher_t.


Record School_t := { School_name : string ; School_address : string }.
Scheme Equality for School_t.



(** Base types for links *)
Record Record_authors_t := { Record_authors_t_lglue : Record_t ; Record_authors_t_rglue : list Author_t }.


Record Article_journal_t := { Article_journal_t_lglue : Article_t ; Article_journal_t_rglue : Journal_t }.


Record Author_records_t := { Author_records_t_lglue : Author_t ; Author_records_t_rglue : list Record_t }.


Record Journal_articles_t := { Journal_articles_t_lglue : Journal_t ; Journal_articles_t_rglue : list Article_t }.


Record Book_publisher_t := { Book_publisher_t_lglue : Book_t ; Book_publisher_t_rglue : Publisher_t }.


Record InCollection_editors_t := { InCollection_editors_t_lglue : InCollection_t ; InCollection_editors_t_rglue : list Editor_t }.


Record InCollection_sponsoredBy_t := { InCollection_sponsoredBy_t_lglue : InCollection_t ; InCollection_sponsoredBy_t_rglue : Organization_t }.


Record InCollection_publisher_t := { InCollection_publisher_t_lglue : InCollection_t ; InCollection_publisher_t_rglue : Publisher_t }.


Record InProceedings_editors_t := { InProceedings_editors_t_lglue : InProceedings_t ; InProceedings_editors_t_rglue : list Editor_t }.


Record InProceedings_organization_t := { InProceedings_organization_t_lglue : InProceedings_t ; InProceedings_organization_t_rglue : Organization_t }.


Record InProceedings_publisher_t := { InProceedings_publisher_t_lglue : InProceedings_t ; InProceedings_publisher_t_rglue : Publisher_t }.


Record MastersThesis_school_t := { MastersThesis_school_t_lglue : MastersThesis_t ; MastersThesis_school_t_rglue : School_t }.


Record Proceedings_editors_t := { Proceedings_editors_t_lglue : Proceedings_t ; Proceedings_editors_t_rglue : list Editor_t }.


Record Proceedings_publisher_t := { Proceedings_publisher_t_lglue : Proceedings_t ; Proceedings_publisher_t_rglue : Publisher_t }.


Record Proceedings_sponsoredBy_t := { Proceedings_sponsoredBy_t_lglue : Proceedings_t ; Proceedings_sponsoredBy_t_rglue : list Organization_t }.


Record PhDThesis_school_t := { PhDThesis_school_t_lglue : PhDThesis_t ; PhDThesis_school_t_rglue : School_t }.


Record Www_editors_t := { Www_editors_t_lglue : Www_t ; Www_editors_t_rglue : list Editor_t }.



(** Data types for element (to build models) *)
Inductive Element : Set :=
  | RecordElement : Record_t -> Element
  | ArticleElement : Article_t -> Element
  | AuthorElement : Author_t -> Element
  | JournalElement : Journal_t -> Element
  | BookElement : Book_t -> Element
  | InCollectionElement : InCollection_t -> Element
  | InProceedingsElement : InProceedings_t -> Element
  | MastersThesisElement : MastersThesis_t -> Element
  | ProceedingsElement : Proceedings_t -> Element
  | PhDThesisElement : PhDThesis_t -> Element
  | WwwElement : Www_t -> Element
  | EditorElement : Editor_t -> Element
  | OrganizationElement : Organization_t -> Element
  | PublisherElement : Publisher_t -> Element
  | SchoolElement : School_t -> Element
.
Scheme Equality for Element.

(** Data types for link (to build models) *)
Inductive Link : Set :=
  | Record_authorsLink : Record_authors_t -> Link
  | Article_journalLink : Article_journal_t -> Link
  | Author_recordsLink : Author_records_t -> Link
  | Journal_articlesLink : Journal_articles_t -> Link
  | Book_publisherLink : Book_publisher_t -> Link
  | InCollection_editorsLink : InCollection_editors_t -> Link
  | InCollection_sponsoredByLink : InCollection_sponsoredBy_t -> Link
  | InCollection_publisherLink : InCollection_publisher_t -> Link
  | InProceedings_editorsLink : InProceedings_editors_t -> Link
  | InProceedings_organizationLink : InProceedings_organization_t -> Link
  | InProceedings_publisherLink : InProceedings_publisher_t -> Link
  | MastersThesis_schoolLink : MastersThesis_school_t -> Link
  | Proceedings_editorsLink : Proceedings_editors_t -> Link
  | Proceedings_publisherLink : Proceedings_publisher_t -> Link
  | Proceedings_sponsoredByLink : Proceedings_sponsoredBy_t -> Link
  | PhDThesis_schoolLink : PhDThesis_school_t -> Link
  | Www_editorsLink : Www_editors_t -> Link
.

(** Meta-types (or kinds, to be used in rules) *)
Inductive ElementKind : Set :=
  | Record_K
  | Article_K
  | Author_K
  | Journal_K
  | Book_K
  | InCollection_K
  | InProceedings_K
  | MastersThesis_K
  | Proceedings_K
  | PhDThesis_K
  | Www_K
  | Editor_K
  | Organization_K
  | Publisher_K
  | School_K
.
Scheme Equality for ElementKind.


Inductive LinkKind : Set :=
  | Record_authors_K
  | Article_journal_K
  | Author_records_K
  | Journal_articles_K
  | Book_publisher_K
  | InCollection_editors_K
  | InCollection_sponsoredBy_K
  | InCollection_publisher_K
  | InProceedings_editors_K
  | InProceedings_organization_K
  | InProceedings_publisher_K
  | MastersThesis_school_K
  | Proceedings_editors_K
  | Proceedings_publisher_K
  | Proceedings_sponsoredBy_K
  | PhDThesis_school_K
  | Www_editors_K
.
Scheme Equality for LinkKind.

(** Reflective functions (typing : correspondence between abstract types (kinds) and model data) *)
Definition getTypeByEKind (k : ElementKind) : Set :=
  match k with
  | Record_K => Record_t
  | Article_K => Article_t
  | Author_K => Author_t
  | Journal_K => Journal_t
  | Book_K => Book_t
  | InCollection_K => InCollection_t
  | InProceedings_K => InProceedings_t
  | MastersThesis_K => MastersThesis_t
  | Proceedings_K => Proceedings_t
  | PhDThesis_K => PhDThesis_t
  | Www_K => Www_t
  | Editor_K => Editor_t
  | Organization_K => Organization_t
  | Publisher_K => Publisher_t
  | School_K => School_t
  end.


Definition lift_EKind k : (getTypeByEKind k) -> Element := 
  match k with
  | Record_K => RecordElement
  | Article_K => ArticleElement
  | Author_K => AuthorElement
  | Journal_K => JournalElement
  | Book_K => BookElement
  | InCollection_K => InCollectionElement
  | InProceedings_K => InProceedingsElement
  | MastersThesis_K => MastersThesisElement
  | Proceedings_K => ProceedingsElement
  | PhDThesis_K => PhDThesisElement
  | Www_K => WwwElement
  | Editor_K => EditorElement
  | Organization_K => OrganizationElement
  | Publisher_K => PublisherElement
  | School_K => SchoolElement
  end.


Definition get_E_data (k : ElementKind) (c : Element) : option (getTypeByEKind k) :=
  match (k,c) as e return (option (getTypeByEKind (fst e))) with
  | (Record_K, RecordElement v)  => Some v
  | (Article_K, ArticleElement v)  => Some v
  | (Author_K, AuthorElement v)  => Some v
  | (Journal_K, JournalElement v)  => Some v
  | (Book_K, BookElement v)  => Some v
  | (InCollection_K, InCollectionElement v)  => Some v
  | (InProceedings_K, InProceedingsElement v)  => Some v
  | (MastersThesis_K, MastersThesisElement v)  => Some v
  | (Proceedings_K, ProceedingsElement v)  => Some v
  | (PhDThesis_K, PhDThesisElement v)  => Some v
  | (Www_K, WwwElement v)  => Some v
  | (Editor_K, EditorElement v)  => Some v
  | (Organization_K, OrganizationElement v)  => Some v
  | (Publisher_K, PublisherElement v)  => Some v
  | (School_K, SchoolElement v)  => Some v
  | (_ , _) => None
  end.


Definition getTypeByLKind (k : LinkKind) : Set :=
  match k with
  | Record_authors_K => Record_authors_t
  | Article_journal_K => Article_journal_t
  | Author_records_K => Author_records_t
  | Journal_articles_K => Journal_articles_t
  | Book_publisher_K => Book_publisher_t
  | InCollection_editors_K => InCollection_editors_t
  | InCollection_sponsoredBy_K => InCollection_sponsoredBy_t
  | InCollection_publisher_K => InCollection_publisher_t
  | InProceedings_editors_K => InProceedings_editors_t
  | InProceedings_organization_K => InProceedings_organization_t
  | InProceedings_publisher_K => InProceedings_publisher_t
  | MastersThesis_school_K => MastersThesis_school_t
  | Proceedings_editors_K => Proceedings_editors_t
  | Proceedings_publisher_K => Proceedings_publisher_t
  | Proceedings_sponsoredBy_K => Proceedings_sponsoredBy_t
  | PhDThesis_school_K => PhDThesis_school_t
  | Www_editors_K => Www_editors_t
  end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with
  | Record_authors_K => Record_authorsLink
  | Article_journal_K => Article_journalLink
  | Author_records_K => Author_recordsLink
  | Journal_articles_K => Journal_articlesLink
  | Book_publisher_K => Book_publisherLink
  | InCollection_editors_K => InCollection_editorsLink
  | InCollection_sponsoredBy_K => InCollection_sponsoredByLink
  | InCollection_publisher_K => InCollection_publisherLink
  | InProceedings_editors_K => InProceedings_editorsLink
  | InProceedings_organization_K => InProceedings_organizationLink
  | InProceedings_publisher_K => InProceedings_publisherLink
  | MastersThesis_school_K => MastersThesis_schoolLink
  | Proceedings_editors_K => Proceedings_editorsLink
  | Proceedings_publisher_K => Proceedings_publisherLink
  | Proceedings_sponsoredBy_K => Proceedings_sponsoredByLink
  | PhDThesis_school_K => PhDThesis_schoolLink
  | Www_editors_K => Www_editorsLink
  end.


Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  match (t,c) as e return (option (getTypeByLKind (fst e))) with
  | (Record_authors_K, Record_authorsLink v)  => Some v
  | (Article_journal_K, Article_journalLink v)  => Some v
  | (Author_records_K, Author_recordsLink v)  => Some v
  | (Journal_articles_K, Journal_articlesLink v)  => Some v
  | (Book_publisher_K, Book_publisherLink v)  => Some v
  | (InCollection_editors_K, InCollection_editorsLink v)  => Some v
  | (InCollection_sponsoredBy_K, InCollection_sponsoredByLink v)  => Some v
  | (InCollection_publisher_K, InCollection_publisherLink v)  => Some v
  | (InProceedings_editors_K, InProceedings_editorsLink v)  => Some v
  | (InProceedings_organization_K, InProceedings_organizationLink v)  => Some v
  | (InProceedings_publisher_K, InProceedings_publisherLink v)  => Some v
  | (MastersThesis_school_K, MastersThesis_schoolLink v)  => Some v
  | (Proceedings_editors_K, Proceedings_editorsLink v)  => Some v
  | (Proceedings_publisher_K, Proceedings_publisherLink v)  => Some v
  | (Proceedings_sponsoredBy_K, Proceedings_sponsoredByLink v)  => Some v
  | (PhDThesis_school_K, PhDThesis_schoolLink v)  => Some v
  | (Www_editors_K, Www_editorsLink v)  => Some v
  | (_ , _) => None
  end.

(** Typeclass Instance *)
Definition MM : Metamodel :=
{|
  ElementType := Element ;
  LinkType := Link ;
  elements_eq_dec := Element_eq_dec ;
|}.


#[export]
Instance DBLPElementDenotation : Denotation Element ElementKind :=
{
  denoteDatatype := getTypeByEKind ;
  unbox := get_E_data ;
  constructor := lift_EKind ;
}.


#[export]
Instance DBLPLinkDenotation : Denotation Link LinkKind :=
{
  denoteDatatype := getTypeByLKind ;
  unbox := get_L_data ;
  constructor := lift_LKind ;
}.


#[export]
Instance MMM : ModelingMetamodel MM :=
{
  elements := DBLPElementDenotation ;
  links := DBLPLinkDenotation ;
}.


Definition M := Model MM.

(** General functions (used in transformations) *)
Fixpoint getRecord_authorsOnLinks (r : Record_t) (l : list Link) : option (list Author_t) :=
 match l with
  | (Record_authorsLink x) :: l1 =>
    if Record_t_beq x.(Record_authors_t_lglue) r
      then (Some x.(Record_authors_t_rglue))
      else getRecord_authorsOnLinks r l1
  | _ :: l1 => getRecord_authorsOnLinks r l1
  | nil => None
 end.


Definition getRecord_authors (m : M) (r : Record_t) : option (list Author_t) :=
  getRecord_authorsOnLinks r m.(modelLinks).


Fixpoint getArticle_journalOnLinks (a : Article_t) (l : list Link) : option (Journal_t) :=
 match l with
  | (Article_journalLink x) :: l1 =>
    if Article_t_beq x.(Article_journal_t_lglue) a
      then (Some x.(Article_journal_t_rglue))
      else getArticle_journalOnLinks a l1
  | _ :: l1 => getArticle_journalOnLinks a l1
  | nil => None
 end.


Definition getArticle_journal (m : M) (a : Article_t) : option (Journal_t) :=
  getArticle_journalOnLinks a m.(modelLinks).


Fixpoint getAuthor_recordsOnLinks (a : Author_t) (l : list Link) : option (list Record_t) :=
 match l with
  | (Author_recordsLink x) :: l1 =>
    if Author_t_beq x.(Author_records_t_lglue) a
      then (Some x.(Author_records_t_rglue))
      else getAuthor_recordsOnLinks a l1
  | _ :: l1 => getAuthor_recordsOnLinks a l1
  | nil => None
 end.


Definition getAuthor_records (m : M) (a : Author_t) : option (list Record_t) :=
  getAuthor_recordsOnLinks a m.(modelLinks).


Fixpoint getJournal_articlesOnLinks (j : Journal_t) (l : list Link) : option (list Article_t) :=
 match l with
  | (Journal_articlesLink x) :: l1 =>
    if Journal_t_beq x.(Journal_articles_t_lglue) j
      then (Some x.(Journal_articles_t_rglue))
      else getJournal_articlesOnLinks j l1
  | _ :: l1 => getJournal_articlesOnLinks j l1
  | nil => None
 end.


Definition getJournal_articles (m : M) (j : Journal_t) : option (list Article_t) :=
  getJournal_articlesOnLinks j m.(modelLinks).


Fixpoint getBook_publisherOnLinks (b : Book_t) (l : list Link) : option (Publisher_t) :=
 match l with
  | (Book_publisherLink x) :: l1 =>
    if Book_t_beq x.(Book_publisher_t_lglue) b
      then (Some x.(Book_publisher_t_rglue))
      else getBook_publisherOnLinks b l1
  | _ :: l1 => getBook_publisherOnLinks b l1
  | nil => None
 end.


Definition getBook_publisher (m : M) (b : Book_t) : option (Publisher_t) :=
  getBook_publisherOnLinks b m.(modelLinks).


Fixpoint getInCollection_editorsOnLinks (i : InCollection_t) (l : list Link) : option (list Editor_t) :=
 match l with
  | (InCollection_editorsLink x) :: l1 =>
    if InCollection_t_beq x.(InCollection_editors_t_lglue) i
      then (Some x.(InCollection_editors_t_rglue))
      else getInCollection_editorsOnLinks i l1
  | _ :: l1 => getInCollection_editorsOnLinks i l1
  | nil => None
 end.


Definition getInCollection_editors (m : M) (i : InCollection_t) : option (list Editor_t) :=
  getInCollection_editorsOnLinks i m.(modelLinks).


Fixpoint getInCollection_sponsoredByOnLinks (i : InCollection_t) (l : list Link) : option (Organization_t) :=
 match l with
  | (InCollection_sponsoredByLink x) :: l1 =>
    if InCollection_t_beq x.(InCollection_sponsoredBy_t_lglue) i
      then (Some x.(InCollection_sponsoredBy_t_rglue))
      else getInCollection_sponsoredByOnLinks i l1
  | _ :: l1 => getInCollection_sponsoredByOnLinks i l1
  | nil => None
 end.


Definition getInCollection_sponsoredBy (m : M) (i : InCollection_t) : option (Organization_t) :=
  getInCollection_sponsoredByOnLinks i m.(modelLinks).


Fixpoint getInCollection_publisherOnLinks (i : InCollection_t) (l : list Link) : option (Publisher_t) :=
 match l with
  | (InCollection_publisherLink x) :: l1 =>
    if InCollection_t_beq x.(InCollection_publisher_t_lglue) i
      then (Some x.(InCollection_publisher_t_rglue))
      else getInCollection_publisherOnLinks i l1
  | _ :: l1 => getInCollection_publisherOnLinks i l1
  | nil => None
 end.


Definition getInCollection_publisher (m : M) (i : InCollection_t) : option (Publisher_t) :=
  getInCollection_publisherOnLinks i m.(modelLinks).


Fixpoint getInProceedings_editorsOnLinks (i : InProceedings_t) (l : list Link) : option (list Editor_t) :=
 match l with
  | (InProceedings_editorsLink x) :: l1 =>
    if InProceedings_t_beq x.(InProceedings_editors_t_lglue) i
      then (Some x.(InProceedings_editors_t_rglue))
      else getInProceedings_editorsOnLinks i l1
  | _ :: l1 => getInProceedings_editorsOnLinks i l1
  | nil => None
 end.


Definition getInProceedings_editors (m : M) (i : InProceedings_t) : option (list Editor_t) :=
  getInProceedings_editorsOnLinks i m.(modelLinks).


Fixpoint getInProceedings_organizationOnLinks (i : InProceedings_t) (l : list Link) : option (Organization_t) :=
 match l with
  | (InProceedings_organizationLink x) :: l1 =>
    if InProceedings_t_beq x.(InProceedings_organization_t_lglue) i
      then (Some x.(InProceedings_organization_t_rglue))
      else getInProceedings_organizationOnLinks i l1
  | _ :: l1 => getInProceedings_organizationOnLinks i l1
  | nil => None
 end.


Definition getInProceedings_organization (m : M) (i : InProceedings_t) : option (Organization_t) :=
  getInProceedings_organizationOnLinks i m.(modelLinks).


Fixpoint getInProceedings_publisherOnLinks (i : InProceedings_t) (l : list Link) : option (Publisher_t) :=
 match l with
  | (InProceedings_publisherLink x) :: l1 =>
    if InProceedings_t_beq x.(InProceedings_publisher_t_lglue) i
      then (Some x.(InProceedings_publisher_t_rglue))
      else getInProceedings_publisherOnLinks i l1
  | _ :: l1 => getInProceedings_publisherOnLinks i l1
  | nil => None
 end.


Definition getInProceedings_publisher (m : M) (i : InProceedings_t) : option (Publisher_t) :=
  getInProceedings_publisherOnLinks i m.(modelLinks).


Fixpoint getMastersThesis_schoolOnLinks (m : MastersThesis_t) (l : list Link) : option (School_t) :=
 match l with
  | (MastersThesis_schoolLink x) :: l1 =>
    if MastersThesis_t_beq x.(MastersThesis_school_t_lglue) m
      then (Some x.(MastersThesis_school_t_rglue))
      else getMastersThesis_schoolOnLinks m l1
  | _ :: l1 => getMastersThesis_schoolOnLinks m l1
  | nil => None
 end.


Definition getMastersThesis_school (_m : M) (m : MastersThesis_t) : option (School_t) :=
  getMastersThesis_schoolOnLinks m _m.(modelLinks).


Fixpoint getProceedings_editorsOnLinks (p : Proceedings_t) (l : list Link) : option (list Editor_t) :=
 match l with
  | (Proceedings_editorsLink x) :: l1 =>
    if Proceedings_t_beq x.(Proceedings_editors_t_lglue) p
      then (Some x.(Proceedings_editors_t_rglue))
      else getProceedings_editorsOnLinks p l1
  | _ :: l1 => getProceedings_editorsOnLinks p l1
  | nil => None
 end.


Definition getProceedings_editors (m : M) (p : Proceedings_t) : option (list Editor_t) :=
  getProceedings_editorsOnLinks p m.(modelLinks).


Fixpoint getProceedings_publisherOnLinks (p : Proceedings_t) (l : list Link) : option (Publisher_t) :=
 match l with
  | (Proceedings_publisherLink x) :: l1 =>
    if Proceedings_t_beq x.(Proceedings_publisher_t_lglue) p
      then (Some x.(Proceedings_publisher_t_rglue))
      else getProceedings_publisherOnLinks p l1
  | _ :: l1 => getProceedings_publisherOnLinks p l1
  | nil => None
 end.


Definition getProceedings_publisher (m : M) (p : Proceedings_t) : option (Publisher_t) :=
  getProceedings_publisherOnLinks p m.(modelLinks).


Fixpoint getProceedings_sponsoredByOnLinks (p : Proceedings_t) (l : list Link) : option (list Organization_t) :=
 match l with
  | (Proceedings_sponsoredByLink x) :: l1 =>
    if Proceedings_t_beq x.(Proceedings_sponsoredBy_t_lglue) p
      then (Some x.(Proceedings_sponsoredBy_t_rglue))
      else getProceedings_sponsoredByOnLinks p l1
  | _ :: l1 => getProceedings_sponsoredByOnLinks p l1
  | nil => None
 end.


Definition getProceedings_sponsoredBy (m : M) (p : Proceedings_t) : option (list Organization_t) :=
  getProceedings_sponsoredByOnLinks p m.(modelLinks).


Fixpoint getPhDThesis_schoolOnLinks (p : PhDThesis_t) (l : list Link) : option (School_t) :=
 match l with
  | (PhDThesis_schoolLink x) :: l1 =>
    if PhDThesis_t_beq x.(PhDThesis_school_t_lglue) p
      then (Some x.(PhDThesis_school_t_rglue))
      else getPhDThesis_schoolOnLinks p l1
  | _ :: l1 => getPhDThesis_schoolOnLinks p l1
  | nil => None
 end.


Definition getPhDThesis_school (m : M) (p : PhDThesis_t) : option (School_t) :=
  getPhDThesis_schoolOnLinks p m.(modelLinks).


Fixpoint getWww_editorsOnLinks (w : Www_t) (l : list Link) : option (list Editor_t) :=
 match l with
  | (Www_editorsLink x) :: l1 =>
    if Www_t_beq x.(Www_editors_t_lglue) w
      then (Some x.(Www_editors_t_rglue))
      else getWww_editorsOnLinks w l1
  | _ :: l1 => getWww_editorsOnLinks w l1
  | nil => None
 end.


Definition getWww_editors (m : M) (w : Www_t) : option (list Editor_t) :=
  getWww_editorsOnLinks w m.(modelLinks).



