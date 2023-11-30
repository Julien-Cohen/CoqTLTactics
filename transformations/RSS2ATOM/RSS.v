(* Automatically generated by Ecore2Coq transformation. *)

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

(* manual insertion here *)
Notation unknown_type := string.

(** Base types for elements *)
Record RSS_t := { RSS_version : unknown_type }.
Scheme Equality for RSS_t.

(* manual : replace all unknown_type by nat *)
Record Channel_t := { Channel_title : unknown_type ; Channel_link : unknown_type ; Channel_description : unknown_type ; Channel_language : unknown_type ; Channel_copyright : unknown_type ; Channel_managingEditor : unknown_type ; Channel_webmaster : unknown_type ; Channel_generator : unknown_type ; Channel_docs : unknown_type ; Channel_ttl : unknown_type ; Channel_rating : unknown_type ; Channel_skipHours : unknown_type ; Channel_pubDate : unknown_type ; Channel_skipDays : unknown_type ; Channel_lastBuildDate : unknown_type }.
Scheme Equality for Channel_t.


Record Item_t := { Item_title : unknown_type ; Item_link : unknown_type ; Item_description : unknown_type ; Item_pubDate : unknown_type ; Item_author : unknown_type ; Item_comments : unknown_type ; Item_guid : unknown_type }.
Scheme Equality for Item_t.


Record Image_t := { Image_url : unknown_type ; Image_title : unknown_type ; Image_link : unknown_type ; Image_description : unknown_type ; Image_width : unknown_type ; Image_height : unknown_type }.
Scheme Equality for Image_t.


Record TextInput_t := { TextInput_title : unknown_type ; TextInput_description : unknown_type ; TextInput_name : unknown_type ; TextInput_link : unknown_type }.
Scheme Equality for TextInput_t.


Record Cloud_t := { Cloud_domain : unknown_type ; Cloud_port : unknown_type ; Cloud_path : unknown_type ; Cloud_registerProcedure : unknown_type ; Cloud_protocol : unknown_type }.
Scheme Equality for Cloud_t.


Record Category_t := { Category_domain : unknown_type ; Category_value : unknown_type }.
Scheme Equality for Category_t.


Record Enclosure_t := { Enclosure_url : unknown_type ; Enclosure_lenght : unknown_type ; Enclosure_type : unknown_type }.
Scheme Equality for Enclosure_t.


Record Source_t := { Source_url : unknown_type ; Source_value : unknown_type }.
Scheme Equality for Source_t.



(** Base types for links *)
Record RSS_channel_t := { RSS_channel_t_lglue : RSS_t ; RSS_channel_t_rglue : Channel_t }.


Record Channel_rss_t := { Channel_rss_t_lglue : Channel_t ; Channel_rss_t_rglue : RSS_t }.


Record Channel_image_t := { Channel_image_t_lglue : Channel_t ; Channel_image_t_rglue : Image_t }.


Record Channel_textInput_t := { Channel_textInput_t_lglue : Channel_t ; Channel_textInput_t_rglue : TextInput_t }.


Record Channel_cloud_t := { Channel_cloud_t_lglue : Channel_t ; Channel_cloud_t_rglue : Cloud_t }.


Record Channel_category_t := { Channel_category_t_lglue : Channel_t ; Channel_category_t_rglue : Category_t }.


Record Channel_items_t := { Channel_items_t_lglue : Channel_t ; Channel_items_t_rglue : list Item_t }.


Record Item_source_t := { Item_source_t_lglue : Item_t ; Item_source_t_rglue : Source_t }.


Record Item_enclosure_t := { Item_enclosure_t_lglue : Item_t ; Item_enclosure_t_rglue : Enclosure_t }.


Record Item_category_t := { Item_category_t_lglue : Item_t ; Item_category_t_rglue : Category_t }.


Record Item_channel_t := { Item_channel_t_lglue : Item_t ; Item_channel_t_rglue : Channel_t }.


Record Image_channel_t := { Image_channel_t_lglue : Image_t ; Image_channel_t_rglue : Channel_t }.


Record TextInput_channel_t := { TextInput_channel_t_lglue : TextInput_t ; TextInput_channel_t_rglue : Channel_t }.


Record Cloud_channel_t := { Cloud_channel_t_lglue : Cloud_t ; Cloud_channel_t_rglue : Channel_t }.


Record Category_channel_t := { Category_channel_t_lglue : Category_t ; Category_channel_t_rglue : Channel_t }.


Record Category_items_t := { Category_items_t_lglue : Category_t ; Category_items_t_rglue : Item_t }.



(** Data types for element (to build models) *)
Inductive Element : Set :=
  | RSSElement : RSS_t -> Element
  | ChannelElement : Channel_t -> Element
  | ItemElement : Item_t -> Element
  | ImageElement : Image_t -> Element
  | TextInputElement : TextInput_t -> Element
  | CloudElement : Cloud_t -> Element
  | CategoryElement : Category_t -> Element
  | EnclosureElement : Enclosure_t -> Element
  | SourceElement : Source_t -> Element
.
Scheme Equality for Element.

(** Data types for link (to build models) *)
Inductive Link : Set :=
  | RSS_channelLink : RSS_channel_t -> Link
  | Channel_rssLink : Channel_rss_t -> Link
  | Channel_imageLink : Channel_image_t -> Link
  | Channel_textInputLink : Channel_textInput_t -> Link
  | Channel_cloudLink : Channel_cloud_t -> Link
  | Channel_categoryLink : Channel_category_t -> Link
  | Channel_itemsLink : Channel_items_t -> Link
  | Item_sourceLink : Item_source_t -> Link
  | Item_enclosureLink : Item_enclosure_t -> Link
  | Item_categoryLink : Item_category_t -> Link
  | Item_channelLink : Item_channel_t -> Link
  | Image_channelLink : Image_channel_t -> Link
  | TextInput_channelLink : TextInput_channel_t -> Link
  | Cloud_channelLink : Cloud_channel_t -> Link
  | Category_channelLink : Category_channel_t -> Link
  | Category_itemsLink : Category_items_t -> Link
.

(** Meta-types (or kinds, to be used in rules) *)
Inductive ElementKind : Set :=
  | RSS_K
  | Channel_K
  | Item_K
  | Image_K
  | TextInput_K
  | Cloud_K
  | Category_K
  | Enclosure_K
  | Source_K
.
Scheme Equality for ElementKind.


Inductive LinkKind : Set :=
  | RSS_channel_K
  | Channel_rss_K
  | Channel_image_K
  | Channel_textInput_K
  | Channel_cloud_K
  | Channel_category_K
  | Channel_items_K
  | Item_source_K
  | Item_enclosure_K
  | Item_category_K
  | Item_channel_K
  | Image_channel_K
  | TextInput_channel_K
  | Cloud_channel_K
  | Category_channel_K
  | Category_items_K
.
Scheme Equality for LinkKind.

(** Reflective functions (typing : correspondence between abstract types (kinds) and model data) *)
Definition getTypeByEKind (k : ElementKind) : Set :=
  match k with
  | RSS_K => RSS_t
  | Channel_K => Channel_t
  | Item_K => Item_t
  | Image_K => Image_t
  | TextInput_K => TextInput_t
  | Cloud_K => Cloud_t
  | Category_K => Category_t
  | Enclosure_K => Enclosure_t
  | Source_K => Source_t
  end.


Definition lift_EKind k : (getTypeByEKind k) -> Element := 
  match k with
  | RSS_K => RSSElement
  | Channel_K => ChannelElement
  | Item_K => ItemElement
  | Image_K => ImageElement
  | TextInput_K => TextInputElement
  | Cloud_K => CloudElement
  | Category_K => CategoryElement
  | Enclosure_K => EnclosureElement
  | Source_K => SourceElement
  end.


Definition get_E_data (k : ElementKind) (c : Element) : option (getTypeByEKind k) :=
  match (k,c) as e return (option (getTypeByEKind (fst e))) with
  | (RSS_K, RSSElement v)  => Some v
  | (Channel_K, ChannelElement v)  => Some v
  | (Item_K, ItemElement v)  => Some v
  | (Image_K, ImageElement v)  => Some v
  | (TextInput_K, TextInputElement v)  => Some v
  | (Cloud_K, CloudElement v)  => Some v
  | (Category_K, CategoryElement v)  => Some v
  | (Enclosure_K, EnclosureElement v)  => Some v
  | (Source_K, SourceElement v)  => Some v
  | (_ , _) => None
  end.


Definition getTypeByLKind (k : LinkKind) : Set :=
  match k with
  | RSS_channel_K => RSS_channel_t
  | Channel_rss_K => Channel_rss_t
  | Channel_image_K => Channel_image_t
  | Channel_textInput_K => Channel_textInput_t
  | Channel_cloud_K => Channel_cloud_t
  | Channel_category_K => Channel_category_t
  | Channel_items_K => Channel_items_t
  | Item_source_K => Item_source_t
  | Item_enclosure_K => Item_enclosure_t
  | Item_category_K => Item_category_t
  | Item_channel_K => Item_channel_t
  | Image_channel_K => Image_channel_t
  | TextInput_channel_K => TextInput_channel_t
  | Cloud_channel_K => Cloud_channel_t
  | Category_channel_K => Category_channel_t
  | Category_items_K => Category_items_t
  end.


Definition lift_LKind k : (getTypeByLKind k) -> Link :=
  match k with
  | RSS_channel_K => RSS_channelLink
  | Channel_rss_K => Channel_rssLink
  | Channel_image_K => Channel_imageLink
  | Channel_textInput_K => Channel_textInputLink
  | Channel_cloud_K => Channel_cloudLink
  | Channel_category_K => Channel_categoryLink
  | Channel_items_K => Channel_itemsLink
  | Item_source_K => Item_sourceLink
  | Item_enclosure_K => Item_enclosureLink
  | Item_category_K => Item_categoryLink
  | Item_channel_K => Item_channelLink
  | Image_channel_K => Image_channelLink
  | TextInput_channel_K => TextInput_channelLink
  | Cloud_channel_K => Cloud_channelLink
  | Category_channel_K => Category_channelLink
  | Category_items_K => Category_itemsLink
  end.


Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=
  match (t,c) as e return (option (getTypeByLKind (fst e))) with
  | (RSS_channel_K, RSS_channelLink v)  => Some v
  | (Channel_rss_K, Channel_rssLink v)  => Some v
  | (Channel_image_K, Channel_imageLink v)  => Some v
  | (Channel_textInput_K, Channel_textInputLink v)  => Some v
  | (Channel_cloud_K, Channel_cloudLink v)  => Some v
  | (Channel_category_K, Channel_categoryLink v)  => Some v
  | (Channel_items_K, Channel_itemsLink v)  => Some v
  | (Item_source_K, Item_sourceLink v)  => Some v
  | (Item_enclosure_K, Item_enclosureLink v)  => Some v
  | (Item_category_K, Item_categoryLink v)  => Some v
  | (Item_channel_K, Item_channelLink v)  => Some v
  | (Image_channel_K, Image_channelLink v)  => Some v
  | (TextInput_channel_K, TextInput_channelLink v)  => Some v
  | (Cloud_channel_K, Cloud_channelLink v)  => Some v
  | (Category_channel_K, Category_channelLink v)  => Some v
  | (Category_items_K, Category_itemsLink v)  => Some v
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
Instance RSSElementDenotation : Denotation Element ElementKind :=
{
  denoteDatatype := getTypeByEKind ;
  unbox := get_E_data ;
  constructor := lift_EKind ;
}.


#[export]
Instance RSSLinkDenotation : Denotation Link LinkKind :=
{
  denoteDatatype := getTypeByLKind ;
  unbox := get_L_data ;
  constructor := lift_LKind ;
}.


#[export]
Instance MMM : ModelingMetamodel MM :=
{
  elements := RSSElementDenotation ;
  links := RSSLinkDenotation ;
}.


Definition M := Model MM.

(** General functions (used in transformations) *)
Fixpoint getRSS_channelOnLinks (r : RSS_t) (l : list Link) : option (Channel_t) :=
 match l with
  | (RSS_channelLink x) :: l1 =>
    if RSS_t_beq x.(RSS_channel_t_lglue) r
      then (Some x.(RSS_channel_t_rglue))
      else getRSS_channelOnLinks r l1
  | _ :: l1 => getRSS_channelOnLinks r l1
  | nil => None
 end.


Definition getRSS_channel (m : M) (r : RSS_t) : option (Channel_t) :=
  getRSS_channelOnLinks r m.(modelLinks).


Fixpoint getChannel_rssOnLinks (c : Channel_t) (l : list Link) : option (RSS_t) :=
 match l with
  | (Channel_rssLink x) :: l1 =>
    if Channel_t_beq x.(Channel_rss_t_lglue) c
      then (Some x.(Channel_rss_t_rglue))
      else getChannel_rssOnLinks c l1
  | _ :: l1 => getChannel_rssOnLinks c l1
  | nil => None
 end.


Definition getChannel_rss (m : M) (c : Channel_t) : option (RSS_t) :=
  getChannel_rssOnLinks c m.(modelLinks).


Fixpoint getChannel_imageOnLinks (c : Channel_t) (l : list Link) : option (Image_t) :=
 match l with
  | (Channel_imageLink x) :: l1 =>
    if Channel_t_beq x.(Channel_image_t_lglue) c
      then (Some x.(Channel_image_t_rglue))
      else getChannel_imageOnLinks c l1
  | _ :: l1 => getChannel_imageOnLinks c l1
  | nil => None
 end.


Definition getChannel_image (m : M) (c : Channel_t) : option (Image_t) :=
  getChannel_imageOnLinks c m.(modelLinks).


Fixpoint getChannel_textInputOnLinks (c : Channel_t) (l : list Link) : option (TextInput_t) :=
 match l with
  | (Channel_textInputLink x) :: l1 =>
    if Channel_t_beq x.(Channel_textInput_t_lglue) c
      then (Some x.(Channel_textInput_t_rglue))
      else getChannel_textInputOnLinks c l1
  | _ :: l1 => getChannel_textInputOnLinks c l1
  | nil => None
 end.


Definition getChannel_textInput (m : M) (c : Channel_t) : option (TextInput_t) :=
  getChannel_textInputOnLinks c m.(modelLinks).


Fixpoint getChannel_cloudOnLinks (c : Channel_t) (l : list Link) : option (Cloud_t) :=
 match l with
  | (Channel_cloudLink x) :: l1 =>
    if Channel_t_beq x.(Channel_cloud_t_lglue) c
      then (Some x.(Channel_cloud_t_rglue))
      else getChannel_cloudOnLinks c l1
  | _ :: l1 => getChannel_cloudOnLinks c l1
  | nil => None
 end.


Definition getChannel_cloud (m : M) (c : Channel_t) : option (Cloud_t) :=
  getChannel_cloudOnLinks c m.(modelLinks).


Fixpoint getChannel_categoryOnLinks (c : Channel_t) (l : list Link) : option (Category_t) :=
 match l with
  | (Channel_categoryLink x) :: l1 =>
    if Channel_t_beq x.(Channel_category_t_lglue) c
      then (Some x.(Channel_category_t_rglue))
      else getChannel_categoryOnLinks c l1
  | _ :: l1 => getChannel_categoryOnLinks c l1
  | nil => None
 end.


Definition getChannel_category (m : M) (c : Channel_t) : option (Category_t) :=
  getChannel_categoryOnLinks c m.(modelLinks).


Fixpoint getChannel_itemsOnLinks (c : Channel_t) (l : list Link) : option (list Item_t) :=
 match l with
  | (Channel_itemsLink x) :: l1 =>
    if Channel_t_beq x.(Channel_items_t_lglue) c
      then (Some x.(Channel_items_t_rglue))
      else getChannel_itemsOnLinks c l1
  | _ :: l1 => getChannel_itemsOnLinks c l1
  | nil => None
 end.


Definition getChannel_items (m : M) (c : Channel_t) : option (list Item_t) :=
  getChannel_itemsOnLinks c m.(modelLinks).


Fixpoint getItem_sourceOnLinks (i : Item_t) (l : list Link) : option (Source_t) :=
 match l with
  | (Item_sourceLink x) :: l1 =>
    if Item_t_beq x.(Item_source_t_lglue) i
      then (Some x.(Item_source_t_rglue))
      else getItem_sourceOnLinks i l1
  | _ :: l1 => getItem_sourceOnLinks i l1
  | nil => None
 end.


Definition getItem_source (m : M) (i : Item_t) : option (Source_t) :=
  getItem_sourceOnLinks i m.(modelLinks).


Fixpoint getItem_enclosureOnLinks (i : Item_t) (l : list Link) : option (Enclosure_t) :=
 match l with
  | (Item_enclosureLink x) :: l1 =>
    if Item_t_beq x.(Item_enclosure_t_lglue) i
      then (Some x.(Item_enclosure_t_rglue))
      else getItem_enclosureOnLinks i l1
  | _ :: l1 => getItem_enclosureOnLinks i l1
  | nil => None
 end.


Definition getItem_enclosure (m : M) (i : Item_t) : option (Enclosure_t) :=
  getItem_enclosureOnLinks i m.(modelLinks).


Fixpoint getItem_categoryOnLinks (i : Item_t) (l : list Link) : option (Category_t) :=
 match l with
  | (Item_categoryLink x) :: l1 =>
    if Item_t_beq x.(Item_category_t_lglue) i
      then (Some x.(Item_category_t_rglue))
      else getItem_categoryOnLinks i l1
  | _ :: l1 => getItem_categoryOnLinks i l1
  | nil => None
 end.


Definition getItem_category (m : M) (i : Item_t) : option (Category_t) :=
  getItem_categoryOnLinks i m.(modelLinks).


Fixpoint getItem_channelOnLinks (i : Item_t) (l : list Link) : option (Channel_t) :=
 match l with
  | (Item_channelLink x) :: l1 =>
    if Item_t_beq x.(Item_channel_t_lglue) i
      then (Some x.(Item_channel_t_rglue))
      else getItem_channelOnLinks i l1
  | _ :: l1 => getItem_channelOnLinks i l1
  | nil => None
 end.


Definition getItem_channel (m : M) (i : Item_t) : option (Channel_t) :=
  getItem_channelOnLinks i m.(modelLinks).


Fixpoint getImage_channelOnLinks (i : Image_t) (l : list Link) : option (Channel_t) :=
 match l with
  | (Image_channelLink x) :: l1 =>
    if Image_t_beq x.(Image_channel_t_lglue) i
      then (Some x.(Image_channel_t_rglue))
      else getImage_channelOnLinks i l1
  | _ :: l1 => getImage_channelOnLinks i l1
  | nil => None
 end.


Definition getImage_channel (m : M) (i : Image_t) : option (Channel_t) :=
  getImage_channelOnLinks i m.(modelLinks).


Fixpoint getTextInput_channelOnLinks (t : TextInput_t) (l : list Link) : option (Channel_t) :=
 match l with
  | (TextInput_channelLink x) :: l1 =>
    if TextInput_t_beq x.(TextInput_channel_t_lglue) t
      then (Some x.(TextInput_channel_t_rglue))
      else getTextInput_channelOnLinks t l1
  | _ :: l1 => getTextInput_channelOnLinks t l1
  | nil => None
 end.


Definition getTextInput_channel (m : M) (t : TextInput_t) : option (Channel_t) :=
  getTextInput_channelOnLinks t m.(modelLinks).


Fixpoint getCloud_channelOnLinks (c : Cloud_t) (l : list Link) : option (Channel_t) :=
 match l with
  | (Cloud_channelLink x) :: l1 =>
    if Cloud_t_beq x.(Cloud_channel_t_lglue) c
      then (Some x.(Cloud_channel_t_rglue))
      else getCloud_channelOnLinks c l1
  | _ :: l1 => getCloud_channelOnLinks c l1
  | nil => None
 end.


Definition getCloud_channel (m : M) (c : Cloud_t) : option (Channel_t) :=
  getCloud_channelOnLinks c m.(modelLinks).


Fixpoint getCategory_channelOnLinks (c : Category_t) (l : list Link) : option (Channel_t) :=
 match l with
  | (Category_channelLink x) :: l1 =>
    if Category_t_beq x.(Category_channel_t_lglue) c
      then (Some x.(Category_channel_t_rglue))
      else getCategory_channelOnLinks c l1
  | _ :: l1 => getCategory_channelOnLinks c l1
  | nil => None
 end.


Definition getCategory_channel (m : M) (c : Category_t) : option (Channel_t) :=
  getCategory_channelOnLinks c m.(modelLinks).


Fixpoint getCategory_itemsOnLinks (c : Category_t) (l : list Link) : option (Item_t) :=
 match l with
  | (Category_itemsLink x) :: l1 =>
    if Category_t_beq x.(Category_items_t_lglue) c
      then (Some x.(Category_items_t_rglue))
      else getCategory_itemsOnLinks c l1
  | _ :: l1 => getCategory_itemsOnLinks c l1
  | nil => None
 end.


Definition getCategory_items (m : M) (c : Category_t) : option (Item_t) :=
  getCategory_itemsOnLinks c m.(modelLinks).



