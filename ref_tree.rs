use core::fmt::{Debug, self};
use std::{fmt::Display, sync::{RwLock, Arc, Weak}, ops::Deref};

/// This struct holds underlying data. It shouldn't be created directly, instead use:
/// [`Node`](struct@Node).
///
/// ```text
/// NodeData
///  | | |
///  | | +- value: T ---------------------------------------+
///  | |                                                    |
///  | |                                        Simple onwership of value
///  | |
///  | +-- parent: RwLock<WeakNodeNodeRef<T>> --------+
///  |                                            |
///  |                 This describes a non-ownership relationship.
///  |                 When a node is dropped, its parent will not be dropped.
///  |
///  +---- children: RwLock<Vec<Child<T>>> ---+
///                                           |
///                 This describes an ownership relationship.
///                 When a node is dropped its children will be dropped as well.
/// ```
pub struct NodeData<T>
where
    T: Display,
{
    value: RwLock<T>,
    depth: RwLock<i32>,
    parent: Parent<T>,
    children: Children<T>,
}

impl<T> fmt::Debug for NodeData<T>
where
  T: Debug + Display,
{
  fn fmt(
    &self,
    f: &mut fmt::Formatter<'_>,
  ) -> fmt::Result {
    let mut parent_msg = String::new();
    if let Some(parent) = self.parent.read().unwrap().upgrade() {
      parent_msg.push_str(format!("📦 {}", parent.value.read().unwrap()).as_str());
    } else {
      parent_msg.push_str("🚫 None");
    }
    f.debug_struct("Node")
      .field("value", &self.value)
      // .field("parent", &self.parent)
      .field("parent", &parent_msg)
      .field("children", &self.children)
      .finish()
  }
}

// Thread safe reference counter for multiple ownership
type NodeDataRef<T> = Arc<NodeData<T>>;
type WeakNodeNodeRef<T> = Weak<NodeData<T>>;

/// Parent relationship is one of non-ownership
/// This is not a `RwLock<NodeDataRef<T>>` which would cause memory leak.
type Parent<T> = RwLock<WeakNodeNodeRef<T>>;

/// Children relationship is one of ownership
type Children<T> = RwLock<Vec<Child<T>>>;
type Child<T> = NodeDataRef<T>;

/// This struct is used to own a [`NodeData`] inside an [`Arc`]. The [`Arc`]
/// can be shared, so that it can have multiple owners. It does not have
/// getter methods for [`NodeData`]'s properties, instead it implements the
/// `Deref` trait to allow it to be used as a [`NodeData`].
///
/// # Shared ownership
///
/// After an instance of this struct is created and it's internal reference is
/// cloned (and given to another) dropping this instance will not drop the cloned
/// internal reference.
///
/// ```text
/// Node { arc_ref: Arc<NodeData> }
///    ▲                 ▲
///    │                 │
///    │      This atomic ref owns the
///    │      `NodeData` & is shared
///    │
///    1. Has methods to manipulate nodes and their children.
///
///    2. When it is dropped, if there are other `Arc`s (shared via
///       `get_copy_of_internal_arc()`) pointing to the same underlying
///       `NodeData`, then the `NodeData` will not be dropped.
///
///    3. This struct is necessary in order for `add_child_and_update_its_parent`
///       to work. Some pointers need to be swapped between 2 nodes for this work
///       (and one of these pointers is a weak one). It is not possible to do this
///       using two `NodeData` objects, without wrapping them in `Arc`s.
/// ```
#[derive(Debug)]
pub struct Node<T: Display> {
    arc_ref: NodeDataRef<T>,
}

impl<T> Deref for Node<T>
where
    T: Display
{
    type Target = NodeData<T>;

    fn deref(&self) -> &Self::Target {
        &self.arc_ref
    }
} 

impl<T> Node<T>
where
    T: Display
{
    pub fn new(value: T) -> Node<T> {
        let new_node = NodeData {
            value: RwLock::new(value),
            depth: RwLock::new(0),
            parent: RwLock::new(Weak::new()),
            children: RwLock::new(Vec::new()),
        };

        let arc_ref = Arc::new(new_node);
        Node { arc_ref }
    }

    pub fn update_value(self: &Self, new_value: T) {
        *self.value.write().unwrap() = new_value;
    }

    pub fn increase_depth(&self) {
        *self.depth.write().unwrap() += 1;
    }

    pub fn decrease_depth(&self) {
        *self.depth.write().unwrap() -= 1;
    }

    pub fn get_copy_of_internal_arc(self: &Self) -> NodeDataRef<T> {
        Arc::clone(&self.arc_ref)
    }

    pub fn create_and_add_child(
        self: &Self,
        value: T,
    ) -> NodeDataRef<T> {
        let new_child = Node::new(value);
        new_child.increase_depth();
        self.add_child_and_update_its_parent(&new_child);
        new_child.get_copy_of_internal_arc()
    }

    pub fn add_child_and_update_its_parent(
        self: &Self,
        child: &Node<T>,
    ) {
        {   // write lock over children vector
            let mut my_children = self.arc_ref.children.write().unwrap();
            my_children.push(child.get_copy_of_internal_arc());
        }   // `my_children` guard dropped

        {   // I can access to parent directly since I implemented Deref trait
            let mut childs_parent = child.parent.write().unwrap();
            *childs_parent = Arc::downgrade(&self.get_copy_of_internal_arc());
        } // `my_parent` guard dropped
    }

    pub fn has_parent(self: &Self) -> bool {
        self.get_parent().is_some()
    }

    pub fn get_parent(self: &Self) -> Option<NodeDataRef<T>> {
        // uses read lock to access parent data
        let my_parent_weak = self.arc_ref.parent.read().unwrap();
        if let Some(my_parent_arc_ref) = my_parent_weak.upgrade() {
            Some(my_parent_arc_ref)
        } else {
            None
        }
    }
}

#[test]
fn test_tree_low_level_node_manipulation() {
    let child_node = Node::new(3);

    {
        let parent_node = Node::new(5);
        parent_node.add_child_and_update_its_parent(&child_node);

        assert_eq!(parent_node.children.read().unwrap().len(), 1);
        assert!(parent_node.parent.read().unwrap().upgrade().is_none());
        assert_eq!(*parent_node.value.read().unwrap(), 5);
        assert_eq!(Arc::weak_count(&parent_node.arc_ref), 1);

        println!("{}: {:#?}", "[parent_node]", parent_node);
        println!("{}: {:#?}", "[child_node]", child_node);

        assert_eq!(Arc::strong_count(&child_node.get_copy_of_internal_arc()), 3);
        assert_eq!(Arc::weak_count(&child_node.get_copy_of_internal_arc()), 0);

        assert_eq!(Arc::strong_count(&parent_node.get_copy_of_internal_arc()), 2);
        assert_eq!(Arc::weak_count(&parent_node.get_copy_of_internal_arc()), 1);

        assert!(child_node.has_parent());
        assert_eq!(*child_node.get_parent().unwrap().value.read().unwrap(), 5);
    } // `parent_node` is dropped here

    // `child_node`'s parent is now `None`, its an orphan
    assert!(!child_node.has_parent());
    assert_eq!(*child_node.get_copy_of_internal_arc().value.read().unwrap(), 3);

    assert_eq!(Arc::strong_count(&child_node.get_copy_of_internal_arc()), 2);
    assert_eq!(Arc::weak_count(&child_node.get_copy_of_internal_arc()), 0);
}

#[test]
fn test_tree_simple_api() {
    let root_node = Node::new(5);
    assert_eq!(*root_node.get_copy_of_internal_arc().value.read().unwrap(), 5);

    {
        let child_node_data_ref = root_node.create_and_add_child(3);
        assert_eq!(*child_node_data_ref.value.read().unwrap(), 3);
        assert_eq!(root_node.get_copy_of_internal_arc().children.read().unwrap().len(), 1);
        assert_eq!(*child_node_data_ref.value.read().unwrap(), *root_node.children.read().unwrap()[0].value.read().unwrap());
    }

    println!("{}: {:#?}", "[tree]", root_node);
}

#[test]
fn test_update_value() {
    let node = Node::new(5);
    assert_eq!(*node.value.read().unwrap(), 5);
    node.update_value(7);
    assert_eq!(*node.value.read().unwrap(), 7);
}
